import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28198.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [0, 1]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [2, 5]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.and, [11, 15]⟩,
  ⟨.or, [10, 16]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.and, [14, 18]⟩,
  ⟨.or, [17, 19]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,20⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 13 ≤ gs.length) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 20, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_28198.Frame

namespace PEqualNP.Outside.L_meta_28198.Reduce
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
end PEqualNP.Outside.L_meta_28198.Reduce

namespace PEqualNP.Outside.L_meta_28198
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 256
def ones : Word := BitVec.allOnes 256
def goal : Word := 0xfffffffffffffffffffffffefffaee00fffffffffffaeeaafffffffefffaee00
def roots : List Word := [
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
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

def assignment (r : Fin 256) : Fin 8 → Bool := fun i => r.val.testBit (([0,1,7,2,3,6,4,5] : List Nat).get i)
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

def witnesses (i : Fin 8) : Fin 256 × Fin 256 := ([(8,9),(8,10),(64,192),(16,20),(1,9),(1,65),(1,17),(1,33)] : List (Fin 256 × Fin 256)).get i
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

end PEqualNP.Outside.L_meta_28198

namespace PEqualNP.Outside.L_meta_28198.Reduce
open PEqualNP.Outside.L_meta_28198

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
end PEqualNP.Outside.L_meta_28198.Reduce

namespace PEqualNP.Outside.L_meta_28198.Reduce
open PEqualNP.Outside.L_meta_28198

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

def sevenRaw : List (BitVec 128) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
def cliqueRaw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def cliqueGoal : BitVec 64 := 0xfffffffefffaee00
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
  if e then ([(8,9),(8,10),(16,20),(1,9),(0,64),(1,17),(1,33)] : List _).get v
  else ([(8,9),(8,10),(16,20),(1,9),(1,65),(1,17),(1,33)] : List _).get v
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
end PEqualNP.Outside.L_meta_28198.Reduce

namespace PEqualNP.Outside.L_meta_28198.ArchivedClique
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
def pt0 : Projection 89 89 := pick [17,19,18,20,23,24,21,22,25,26,27,28,29,31,32,30,33,0,2,1,3,6,7,4,5,8,9,10,11,12,15,13,14,16,34,36,35,37,38,41,42,39,40,43,44,46,45,47,50,51,48,49,52,61,62,63,64,66,67,65,68,53,54,55,56,59,57,58,60,79,81,80,82,83,86,87,84,85,88,69,71,70,72,73,76,77,74,75,78] rfl (by decide +kernel) (by decide)
def pti0 : Projection 89 89 := pick [17,19,18,20,23,24,21,22,25,26,27,28,29,31,32,30,33,0,2,1,3,6,7,4,5,8,9,10,11,12,15,13,14,16,34,36,35,37,38,41,42,39,40,43,44,46,45,47,50,51,48,49,52,61,62,63,64,66,67,65,68,53,54,55,56,59,57,58,60,79,81,80,82,83,86,87,84,85,88,69,71,70,72,73,76,77,74,75,78] rfl (by decide +kernel) (by decide)
def pc1_0 : Projection 40 40 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,30,31,33,32,34,25,26,28,27,29,35,36,38,37,39] rfl (by decide +kernel) (by decide)
def pci1_0 : Projection 40 40 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,30,31,33,32,34,25,26,28,27,29,35,36,38,37,39] rfl (by decide +kernel) (by decide)
def pc1_1 : Projection 40 40 := pick [1,0,2,3,4,26,25,27,28,29,31,30,32,33,34,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,36,35,37,38,39] rfl (by decide +kernel) (by decide)
def pci1_1 : Projection 40 40 := pick [1,0,2,3,4,26,25,27,28,29,31,30,32,33,34,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,36,35,37,38,39] rfl (by decide +kernel) (by decide)
def pc2_2 : Projection 40 40 := pick [37,38,35,36,39,7,8,5,6,9,27,28,25,26,29,22,23,20,21,24,17,18,15,16,19,12,13,10,11,14,32,33,30,31,34,2,3,0,1,4] rfl (by decide +kernel) (by decide)
def pci2_2 : Projection 40 40 := pick [37,38,35,36,39,7,8,5,6,9,27,28,25,26,29,22,23,20,21,24,17,18,15,16,19,12,13,10,11,14,32,33,30,31,34,2,3,0,1,4] rfl (by decide +kernel) (by decide)
def pc7_1 : Projection 20 20 := pick [8,9,10,11,16,17,18,19,0,1,2,3,12,13,14,15,4,5,6,7] rfl (by decide +kernel) (by decide)
def pci7_1 : Projection 20 20 := pick [8,9,10,11,16,17,18,19,0,1,2,3,12,13,14,15,4,5,6,7] rfl (by decide +kernel) (by decide)
def pc8_0 : Projection 16 16 := pick [1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11] rfl (by decide +kernel) (by decide)
def pci8_0 : Projection 16 16 := pick [1,0,2,3,5,4,6,7,13,12,14,15,9,8,10,11] rfl (by decide +kernel) (by decide)
def pc11_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pci11_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pc11_2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def pci11_2 : Projection 20 20 := pick [8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,16,17,18,19] rfl (by decide +kernel) (by decide)
def pc11_3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def pci11_3 : Projection 20 20 := pick [12,14,13,15,8,10,9,11,4,6,5,7,0,2,1,3,16,18,17,19] rfl (by decide +kernel) (by decide)
def pc13_0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pci13_0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pc15_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pci15_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pc16_0 : Projection 16 16 := pick [14,13,12,15,6,5,4,7,10,9,8,11,2,1,0,3] rfl (by decide +kernel) (by decide)
def pci16_0 : Projection 16 16 := pick [14,13,12,15,6,5,4,7,10,9,8,11,2,1,0,3] rfl (by decide +kernel) (by decide)
def pc18_0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def pci18_0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def pc18_1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pci18_1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pc18_3 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def pci18_3 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def pc18_4 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def pci18_4 : Projection 12 12 := pick [10,9,8,11,6,5,4,7,2,1,0,3] rfl (by decide +kernel) (by decide)
def pjt_0 : Projection 89 35 := pick [11,14,15,16,9,55,58,59,60,53,28,30,32,33,26,63,65,67,68,61,37,40,42,43,34,72,75,77,78,69,82,85,87,88,79] rfl (by decide +kernel) (by decide)
def pjt_1 : Projection 89 40 := pick [2,5,6,8,0,19,22,23,25,17,46,49,50,52,44,27,30,31,33,26,62,65,66,68,61,36,40,41,43,34,71,75,76,78,69,81,85,86,88,79] rfl (by decide +kernel) (by decide)
def pjt_2 : Projection 89 40 := pick [1,4,7,8,0,18,21,24,25,17,45,48,51,52,44,10,13,15,16,9,54,57,59,60,53,35,39,42,43,34,70,74,77,78,69,80,84,87,88,79] rfl (by decide +kernel) (by decide)
def pjt_3 : Projection 89 24 := pick [20,24,25,17,47,51,52,44,56,59,60,53,29,32,33,26,64,67,68,61,83,87,88,79] rfl (by decide +kernel) (by decide)
def pjt_6 : Projection 89 20 := pick [30,31,33,26,65,66,68,61,40,41,43,34,75,76,78,69,85,86,88,79] rfl (by decide +kernel) (by decide)
def pjt_7 : Projection 89 20 := pick [13,15,16,9,57,59,60,53,39,42,43,34,74,77,78,69,84,87,88,79] rfl (by decide +kernel) (by decide)
def pjt_8 : Projection 89 16 := pick [55,59,60,53,28,32,33,26,63,67,68,61,82,87,88,79] rfl (by decide +kernel) (by decide)
def pjt_9 : Projection 89 16 := pick [11,14,16,9,55,58,60,53,63,65,68,61,72,75,78,69] rfl (by decide +kernel) (by decide)
def pjt_10 : Projection 89 12 := pick [11,14,15,9,28,30,32,26,37,40,42,34] rfl (by decide +kernel) (by decide)
def pjt_11 : Projection 89 20 := pick [19,23,25,17,46,50,52,44,27,31,33,26,62,66,68,61,81,86,88,79] rfl (by decide +kernel) (by decide)
def pjt_12 : Projection 89 16 := pick [2,5,8,0,46,49,52,44,62,65,68,61,71,75,78,69] rfl (by decide +kernel) (by decide)
def pjt_13 : Projection 89 16 := pick [2,5,6,0,19,22,23,17,27,30,31,26,36,40,41,34] rfl (by decide +kernel) (by decide)
def pjt_14 : Projection 89 16 := pick [18,24,25,17,45,51,52,44,54,59,60,53,80,87,88,79] rfl (by decide +kernel) (by decide)
def pjt_15 : Projection 89 20 := pick [1,4,8,0,45,48,52,44,10,13,16,9,54,57,60,53,70,74,78,69] rfl (by decide +kernel) (by decide)
def pjt_16 : Projection 89 16 := pick [1,4,7,0,18,21,24,17,10,13,15,9,35,39,42,34] rfl (by decide +kernel) (by decide)
def pjt_18 : Projection 89 12 := pick [39,41,43,34,74,76,78,69,84,86,88,79] rfl (by decide +kernel) (by decide)
def pjt_20 : Projection 89 6 := pick [30,31,26,40,41,34] rfl (by decide +kernel) (by decide)
def pjt_23 : Projection 89 6 := pick [55,60,53,63,68,61] rfl (by decide +kernel) (by decide)
def pjt_26 : Projection 89 6 := pick [46,52,44,62,68,61] rfl (by decide +kernel) (by decide)
def pjt_27 : Projection 89 6 := pick [19,23,17,27,31,26] rfl (by decide +kernel) (by decide)
def pjt_29 : Projection 89 6 := pick [45,52,44,54,60,53] rfl (by decide +kernel) (by decide)
def pjt_31 : Projection 89 6 := pick [1,4,0,10,13,9] rfl (by decide +kernel) (by decide)
def f0 : ℕ := 0x1110f0
def f1 : ℕ := 0x1110ff
def f2 : ℕ := 0x222f0f
def f3 : ℕ := 0x444ff0
def f4 : ℕ := 0x111110ff00
def f5 : ℕ := 0x22222000ff
def f6 : ℕ := 0x22222f0f00
def f7 : ℕ := 0x44444ff0f0
def f8 : ℕ := 0x111110ff0f
def f11 : ℕ := 0x22222f0f0f
def f12 : ℕ := 0xff
def f13 : ℕ := 0x11111000ff
def f14 : ℕ := 0x111110ffff
def f17 : ℕ := 0x44444ff000
def f18 : ℕ := 0x140502820180a0503020180000000000000000000000
def f19 : ℕ := 0x1605828281c0b05038281c000000001ff00003fe01ff
def f20 : ℕ := 0x5c17078b0582e0f0b0b05800001fe0000003fc000000
def f21 : ℕ := 0x6018040c06030080c0c060007fe000000ffc0001ffff
def f22 : ℕ := 0x11a4693139148d2622939140000001fe000000001fe00
def f23 : ℕ := 0x180601810180c0303010181ff800000000ffffffe0000
def f24 : ℕ := 0x20080202020100404020201fffffffffff00000000000
def f25 : ℕ := 0x333330ffff
def f26 : ℕ := 0xf00
def f27 : ℕ := 0x33333fff0f
def f30 : ℕ := 0xff00
def f33 : ℕ := 0x111100ff
def f34 : ℕ := 0x2222f00f
def f37 : ℕ := 0x4444f0f0
def f38 : ℕ := 0x55550f00
def f39 : ℕ := 0x1f
def f40 : ℕ := 0x8421084210000007fff
def f41 : ℕ := 0x108421084207fe0f801f
def f42 : ℕ := 0x2108421084f83e0003e0
def f43 : ℕ := 0x294a5294a50001ff8000
def f44 : ℕ := 0x4210842108ffc1f07c00
def f45 : ℕ := 0x18c6318c6307fe0fffff
def f46 : ℕ := 0x8421084210000007fe0
def f48 : ℕ := 0x3e0
def f49 : ℕ := 0xf8000
def f52 : ℕ := 0x108421084207fe00001f
def f59 : ℕ := 0x10842108420000000000
def f60 : ℕ := 0x18c6318c630001ffffff
def f61 : ℕ := 0x2108421084f83e0f83e0
def f62 : ℕ := 0x18c6318c630001ff8000
def f63 : ℕ := 0x18c6318c6307ffff801f
def f64 : ℕ := 0x7fe00001f
def f65 : ℕ := 0x18c6318c6307ffffffff
def f66 : ℕ := 0x7fe000000
def f68 : ℕ := 0x3e000000
def f71 : ℕ := 0x2108421084f8000f83e0
def f72 : ℕ := 0x7c0000000
def f74 : ℕ := 0x4210842108f801f07c00
def f75 : ℕ := 0x200800080401000080804000000001ff00003fe01ff
def f76 : ℕ := 0x5e17878b85c2f0f0b8b85c00001fe01ff003fffe01ff
def f77 : ℕ := 0x40100408040200808080400000000000000000000000
def f78 : ℕ := 0x7c1f078f0783e0f0f0f078007fffe0000ffffc01ffff
def f79 : ℕ := 0x1c0703830180e07030301800001fe0000003fc000000
def f80 : ℕ := 0x247
def f81 : ℕ := 0x278
def f82 : ℕ := 0xf000
def f83 : ℕ := 0x4444fff0
def f90 : ℕ := 0x11110ff0
def f91 : ℕ := 0x2222f0f0
def f94 : ℕ := 0x1111110ff0ff
def f95 : ℕ := 0x222222f0f00f
def f97 : ℕ := 0x1ff
def f98 : ℕ := 0x2008000402010000404020007fe000000ffc0001ffff
def f99 : ℕ := 0x7e1f878f87c3f0f0f8f87c007fffe01fffffffffffff
def f100 : ℕ := 0x2008000402010000404020007fe000000ffc0001fe00
def f101 : ℕ := 0x5e17878b85c2f0f0b8b85c00001fe01ff003fffe0000
def f102 : ℕ := 0x1fe00
def f103 : ℕ := 0x13a4e93179349d262697934007fe01fe00ffc0001ffff
def f104 : ℕ := 0x2008000402010000404020007fe000000ffc000001ff
def f105 : ℕ := 0x11a4693139148d2622939140000001fe0000000000000
def f106 : ℕ := 0xffc00000000
def f107 : ℕ := 0x1a06818141a0d03034141a1ffffe000000fffffffffff
def f108 : ℕ := 0x2008000402010000404020007fe0000000000001ffff
def f109 : ℕ := 0x180601810180c0303010181ff800000000003fffe0000
def f110 : ℕ := 0x7fe00000000000000000
def f111 : ℕ := 0x22088202422110404424221fffffffffffffc0001ffff
def f112 : ℕ := 0x200800040201000040402000000000000ffc0001ffff
def f113 : ℕ := 0x20080202020100404020201ff801ffffff00000000000
def f114 : ℕ := 0x1a0683038140d0602838140000000000000000000000
def f115 : ℕ := 0x15e57979b95caf2f2b9b95c00001ffffff003ffffffff
def f116 : ℕ := 0x441104880482209090804800001fe01ff003fffe01ff
def f117 : ℕ := 0x100401010100802020101000000001fe000000001fe00
def f118 : ℕ := 0x3fffe0000
def f119 : ℕ := 0x1de779f9b9dcef3f3b9b9ddff801fe01ffffffffe01ff
def f120 : ℕ := 0x5e17878b85c2f0f0b8b85c00001fe01ff000000001ff
def f121 : ℕ := 0x180601810180c0303010181ff800000000ffc00000000
def f122 : ℕ := 0x1fe01ff00000000000
def f123 : ℕ := 0x25e97a7aba5d2f4f4baba5dfffffffffff003fffe01ff
def f124 : ℕ := 0x5e17878b85c2f0f0b8b85c00000000000003fffe01ff
def f125 : ℕ := 0x20080202020100404020201ffffe01fe0000000000000
def f126 : ℕ := 0x100401010100802020101000000000000000000000000
def f127 : ℕ := 0x3333ffff
def f128 : ℕ := 0x5555fff0
def f130 : ℕ := 0x19a669b13994cd363293995ff80001fe00ffffffffe00
def f131 : ℕ := 0x1a0683038140d0602838140000001fe000000001fe00
def f132 : ℕ := 0x8020080008040101000081ff800000000ffffffe0000
def f133 : ℕ := 0x1fe0000000000000
def f134 : ℕ := 0x31ac6b333b158d6662b3b15fffffffffff0000001fe00
def f135 : ℕ := 0x11a4693139148d262293914000000000000000001fe00
def f136 : ℕ := 0x20080202020100404020201ffffffe01ff00000000000
def f137 : ℕ := 0x1ff80000000000000000000
def f138 : ℕ := 0x380e03830381c0707030381fffffffffffffffffe0000
def f139 : ℕ := 0x180601810180c030301018000000000000ffffffe0000
def f140 : ℕ := 0x20080202020100404020200007ffffffff00000000000
def f141 : ℕ := 0x180603030100c0602030100000000000000000000000
def f143 : ℕ := 0x33330fff
def f144 : ℕ := 0x4444ff0f
def f147 : ℕ := 0x3333330fff00
def f149 : ℕ := 0x444444ff0ff0
def f154 : ℕ := 0x401004080402008080804000000000000000000001ff
def f155 : ℕ := 0x15e57979b95caf2f2b9b95c00001fffe00003fc01fe00
def f156 : ℕ := 0x1e07838381c0f07038381c00001fe01ff003fffe0000
def f157 : ℕ := 0x5e17878b85c2f0f0b8b85c00001fe0000003fc000000
def f158 : ℕ := 0x1ff00003fe01ff
def f159 : ℕ := 0x4010040804020080808040000000000000000001fe00
def f160 : ℕ := 0x17e5f979f97cbf2f2f9f97c007fffffe00ffffc01ffff
def f161 : ℕ := 0x11e47939391c8f27239391c00001fffe00003fc000000
def f162 : ℕ := 0x1e0781c1c1e0f0383c1c1e1ffffe000000fffffffffff
def f163 : ℕ := 0x6018040c06030080c0c060007fe0000000000001ffff
def f164 : ℕ := 0x26098242c26130484c2c261fffffffffffffc0001ffff
def f165 : ℕ := 0x6018040c06030080c0c06000000000000ffc0001ffff
def f166 : ℕ := 0x1004010101008020201010000000000000003fc000000
def f167 : ℕ := 0x1de779f9b9dcef3f3b9b9ddff801fffe00ffffffffe00
def f168 : ℕ := 0x5e17878b85c2f0f0b8b85c00001fffe000000001fe00
def f169 : ℕ := 0x8020080008040101000081ff800000000ffc03fe0000
def f170 : ℕ := 0x1fffe0000000000000
def f171 : ℕ := 0x35ed7b7bbb5daf6f6bbbb5dfffffffffff003fc01fe00
def f172 : ℕ := 0x15e57979b95caf2f2b9b95c00000000000003fc01fe00
def f173 : ℕ := 0x20080202020100404020201ffffe0001ff00000000000
def f174 : ℕ := 0x441104880482209090804800001fe0000003fc000000
def f175 : ℕ := 0x102409010904812020909040000001fe000000001fe00
def f176 : ℕ := 0x3fc000000
def f177 : ℕ := 0x1dc771f9b1d8ee3f3b1b1d9ff801fe0000ffffffe0000
def f178 : ℕ := 0x5c17078b0582e0f0b0b05800001fe000000000000000
def f179 : ℕ := 0x180601810180c0303010181ff800000000ffc03fe0000
def f180 : ℕ := 0x1fe000000000000000
def f182 : ℕ := 0x5ad6b5ad6bffc1fffc00
def f186 : ℕ := 0x6318c6318cffffffffe0
def f187 : ℕ := 0x421084210807c1f07c00
def f189 : ℕ := 0x25c9727ab2592e4f4b2b259fffffffffff003fc000000
def f190 : ℕ := 0x5c17078b0582e0f0b0b05800001fe01ff003fc000000
def f191 : ℕ := 0x2008000804010000808040000000000000003fe01ff
def f192 : ℕ := 0x17a5e971f974bd2e2e9f974007fe01fe00ffc0001ffff
def f193 : ℕ := 0x6018040c06030080c0c060007fe000000ffc000001ff
def f194 : ℕ := 0x6666ffff
def f195 : ℕ := 0x7777fff0
def f196 : ℕ := 0x4010040804020080808040007fe00000000000000000
def f197 : ℕ := 0x2222ff0f
def f198 : ℕ := 0x2449124a824922494928249ffffffe01ff003fc000000
def f199 : ℕ := 0x444440f0f0
def f200 : ℕ := 0x55555ffff0
def f201 : ℕ := 0x3dcf73fbb3d9ee7f7b3b3d9fffffffffffffffffe0000
def f202 : ℕ := 0x25c9727ab2592e4f4b2b258007ffffffff00000000000
def f203 : ℕ := 0x5c17078b0582e0f0b0b05800000000000003fc000000
def f204 : ℕ := 0x20080202020100404020201ffffe01ffff00000000000
def f205 : ℕ := 0x487
def f206 : ℕ := 0x4b8
def f209 : ℕ := 0x5294a5294afffff07c1f
def f210 : ℕ := 0x11100f
def f211 : ℕ := 0x444f00
def f212 : ℕ := 0x18c6318c6307fe007fff
def f213 : ℕ := 0x108421084207fe000000
def f214 : ℕ := 0x10842108420001ff8000
def f215 : ℕ := 0x294a5294a5f83e0fffff
def f216 : ℕ := 0x8421084210000007c1f
def f217 : ℕ := 0x2108421084f83e0f8000
def f218 : ℕ := 0x7c00
def f219 : ℕ := 0x4a5294a529ffc1f07fff
def f220 : ℕ := 0x84210842100000003ff
def f221 : ℕ := 0x4210842108ffc1f00000
def f222 : ℕ := 0x1084210842000000001f
def f223 : ℕ := 0x8421084210001ffffe0
def f224 : ℕ := 0x318c6318c6fffe0f83ff
def f225 : ℕ := 0x108421084207c000001f
def f226 : ℕ := 0x1084210842003e00001f
def f227 : ℕ := 0xf83e0
def f228 : ℕ := 0x39ce739ce7f83fffffff
def f229 : ℕ := 0x18c6318c630001f07c1f
def f230 : ℕ := 0x2108421084f83e000000
def f231 : ℕ := 0x1f07c00
def f232 : ℕ := 0x5ad6b5ad6bffc1ffffff
def f233 : ℕ := 0x18c6318c6300000f83ff
def f234 : ℕ := 0x4210842108ffc0000000
def f235 : ℕ := 0xf800000000
def f236 : ℕ := 0x2108421084003e0f83e0
def f248 : ℕ := 0x4210842103ff0001f
def f249 : ℕ := 0x6318c6318000ffc00
def f250 : ℕ := 0x842108427c1f07c00
def f251 : ℕ := 0xa5294a528000003ff
def f252 : ℕ := 0x6318c63183ffffc1f
def f255 : ℕ := 0x1f00000
def f256 : ℕ := 0xc6318c637fff07c1f
def f260 : ℕ := 0x6218840c86431080c8c864007fe0001ffffc03ffffff
def f261 : ℕ := 0x200800080401000080804000000001ff00003fe0000
def f262 : ℕ := 0x6018040c06030080c0c060007fe000000ffc0001fe00
def f263 : ℕ := 0x2008000804010000808040000000000000000000000
def f264 : ℕ := 0x11a4693139148d2622939140000001ffff00003ffffff
def f265 : ℕ := 0x1184613131108c2622131100000001fe000000001fe00
def f266 : ℕ := 0x3fe0000
def f267 : ℕ := 0x182609810984c1303090985ff8000001ffffffffe01ff
def f268 : ℕ := 0x200800080401000080804000000001ff000000001ff
def f269 : ℕ := 0x180601810180c0303010181ff800000000ffffc000000
def f270 : ℕ := 0x1ff00000000000
def f271 : ℕ := 0x20280a020a05014040a0a05fffffffffff00003fe01ff
def f272 : ℕ := 0x20080202020100404020201ffffffffe0000000000000
def f273 : ℕ := 0x108421084207ffff801f
def f274 : ℕ := 0x1ff8000
def f275 : ℕ := 0x318c6318c6f83fff83e0
def f276 : ℕ := 0x10842108420001f00000
def f277 : ℕ := 0x5294a5294affc1fffc00
def f278 : ℕ := 0x108421084200000f8000
def f279 : ℕ := 0x4210842108ffc0007c00
def f280 : ℕ := 0x48120509040240a080904000001fe0000003fc000000
def f281 : ℕ := 0x33333f0fff
def f289 : ℕ := 0x761d868e87c3b0d0f8e87c007fe0001ffffc03ffffff
def f290 : ℕ := 0x6ff
def f291 : ℕ := 0x12048202814090402828140000000000000000000000
def f292 : ℕ := 0x11e47939391c8f27239391c0000001ffff00003ffffff
def f293 : ℕ := 0x401008000802010100008000000001ff00003fe01ff
def f294 : ℕ := 0x108421111100842220111000000001fe000000001fe00
def f297 : ℕ := 0x5415068a0582a0d0b0a0580000000000000000000000
def f298 : ℕ := 0x196659a9299ccb35339299dff8000001ffffffffe01ff
def f299 : ℕ := 0x80201010000402000100000001fe0000003fc000000
def f300 : ℕ := 0x2208800482411000484824007fe0001ffffc03ffffff
def f301 : ℕ := 0x140502820180a05030201800000000000003fc000000
def f302 : ℕ := 0x48120509040240a080904000001fe000000000000000
def f303 : ℕ := 0x182609810984c1303090985ff8000001ffffc03fe01ff
def f304 : ℕ := 0x1204820281409040282814000000000000000001fe00
def f305 : ℕ := 0x17e5f979f97cbf2f2f9f97c007fe01ffffffc03ffffff
def f306 : ℕ := 0x6419048c06832090d0c068007fe0001ffffc03fe01ff
def f307 : ℕ := 0x108421111100842220111000000001fe0000000000000
def f308 : ℕ := 0x1605828281c0b05038281c000000001ffffc03fe01ff
def f309 : ℕ := 0x1f67d9e9e9fcfb3d3f9e9fdffffe0001fffffffffffff
def f310 : ℕ := 0x6018040c06030080c0c060007fe0000000000001fe00
def f311 : ℕ := 0x180601810180c0303010181ff800000000003fc000000
def f312 : ℕ := 0x7fe0001ff00000000000
def f313 : ℕ := 0x77777fffff
def f314 : ℕ := 0x2769da6aea7d3b4d4faea7dfffffffffffffc03ffffff
def f315 : ℕ := 0x761d868e87c3b0d0f8e87c00000000000ffc03ffffff
def f316 : ℕ := 0x20080202020100404020201ff801fffe0000000000000
def f317 : ℕ := 0x112449212914892422929140000000000000000000000
def f318 : ℕ := 0x19e679b9399ccf37339399dff80001fffffffffffffff
def f319 : ℕ := 0x8020101000040200010000000001fe000000001fe00
def f320 : ℕ := 0x8421088008842111100089ff8000001ffffffffe01ff
def f321 : ℕ := 0x1ff8000001ff00000000000
def f322 : ℕ := 0x396e5bab2b9dcb7573b2b9dfffffffffffffffffe01ff
def f323 : ℕ := 0x196659a9299ccb35339299c00000000000ffffffe01ff
def f324 : ℕ := 0x20080202020100404020200007fffffe0000000000000
def f325 : ℕ := 0x1605828281c0b05038281c000000001ff000000001ff
def f327 : ℕ := 0x55555ff0ff
def f342 : ℕ := 0x21685a2a2a1d0b4543a2a1dfffffffffff00003fe01ff
def f343 : ℕ := 0x140502820180a05030201800001fe000000000000000
def f344 : ℕ := 0x48120509040240a080904000000000000003fc000000
def f345 : ℕ := 0x20280a020a05014040a0a05ffffe01ffff00003fe01ff
def f346 : ℕ := 0xffc03fe0000
def f347 : ℕ := 0x761d868e87c3b0d0f8e87c007fe0001ff0000001ffff
def f348 : ℕ := 0x1605828281c0b05038281c007fe0001ff00003fe01ff
def f349 : ℕ := 0x6018040c06030080c0c06000000000000ffc0001fe00
def f350 : ℕ := 0x12048202814090402828140000001fe0000000000000
def f351 : ℕ := 0x31ec7b3b3b1d8f6763b3b1dfffffffffff00003ffffff
def f352 : ℕ := 0x10842111110084222011100000000000000000001fe00
def f353 : ℕ := 0x2048120a020902414120209ffffffe01ff00003fe01ff
def f354 : ℕ := 0x1ff80000000000003fe0000
def f355 : ℕ := 0x180601810180c030301018000000000000ffffc000000
def f356 : ℕ := 0x21685a2a2a1d0b4543a2a1c007ffffffff000000001ff
def f358 : ℕ := 0x1605828281c0b05038281c0000000000000003fe01ff
def f361 : ℕ := 0x1605828281c0b05038281c000000001ff00003fe0000
def f363 : ℕ := 0x55550fff
def f364 : ℕ := 0x294a5294a50001ffffff
def f365 : ℕ := 0x1084210847fe0f83e0
def f366 : ℕ := 0x3333f0ff
def f371 : ℕ := 0x7c1f078f0783e0f0f0f078007fffe0000ffffc01fe00
def f372 : ℕ := 0x17a5e971f974bd2e2e9f974007fe01fe00ffc0001fe00
def f373 : ℕ := 0x6018040c06030080c0c060007fe000000ffc00000000
def f374 : ℕ := 0x1e0781c1c1e0f0383c1c1e1ffffe000000ffffffffe00
def f375 : ℕ := 0x26098242c26130484c2c261fffffffffffffc0001fe00
def f379 : ℕ := 0x3333ff0f
def f380 : ℕ := 0x5555ffff
def f381 : ℕ := 0x7fe000000000000001ff
def f382 : ℕ := 0x21685a2a2a1d0b4543a2a1dff801ffffff00003fe0000
def f386 : ℕ := 0x25c9727ab2592e4f4b2b259ffffffffe00003fc000000
def f387 : ℕ := 0x26098242c26130484c2c261ffffffffe00ffc0001ffff
def f388 : ℕ := 0x31ac6b333b158d6662b3b15ffffffffe000000001fe00
def f389 : ℕ := 0x20080202020100404020201ffffffe000000000000000
def f390 : ℕ := 0x380e03830381c0707030381ffffffffe00ffffffe0000
def f391 : ℕ := 0x66666fff0f
def f408 : ℕ := 0x140502820180a05030201800000000000000000001ff
def f409 : ℕ := 0x681a050d060340a0c0d060007fffe0000ffffc01fe00
def f410 : ℕ := 0x16b5ad6b5ffe0fffe0
def f411 : ℕ := 0x180603030100c060203010000000000000000001fe00
def f412 : ℕ := 0x6419048c06832090d0c068007fffe0000ffffc0001ff
def f413 : ℕ := 0x102409010904812020909040000001fe0000000000000
def f414 : ℕ := 0xffffc000000
def f415 : ℕ := 0x1fc7f1f9f1f8fe3f3f1f1f9ffffffe0000fffffffffff
def f416 : ℕ := 0x7c1f078f0783e0f0f0f078007fffe00000000001ffff
def f417 : ℕ := 0x180601810180c0303010181ff80000000000003fe0000
def f418 : ℕ := 0x7fffe000000000000000
def f421 : ℕ := 0x5294a5294afffffffc1f
def f422 : ℕ := 0x27c9f27af2793e4f4f2f279fffffffffffffffc01ffff
def f423 : ℕ := 0x7c1f078f0783e0f0f0f07800000000000ffffc01ffff
def f424 : ℕ := 0x20080202020100404020201ff80001ffff00000000000
def f425 : ℕ := 0x333fff
def f426 : ℕ := 0x55500f
def f428 : ℕ := 0x14a5294a57ffff83ff
def f438 : ℕ := 0x8421084210001ff8000
def f445 : ℕ := 0x360d828683c1b05078683c007fe0001ffffc03ffffff
def f446 : ℕ := 0xe739ce738000fffff
def f452 : ℕ := 0x1605828281c0b05038281c0000000000000000000000
def f453 : ℕ := 0x148521519140a42a281914000001fffe00003fc01fe00
def f454 : ℕ := 0x1ad6b5ad6ffe0f83ff
def f460 : ℕ := 0x18c6318c67ffffffe0
def f461 : ℕ := 0x4440f0
def f468 : ℕ := 0x4010080008020101000080000000000000000000000
def f469 : ℕ := 0x5615868a85c2b0d0b8a85c00001fe01ff003fffe01ff
def f470 : ℕ := 0x1204820281409040282814000000001ff00003fe01ff
def f471 : ℕ := 0x401004080402008080804000001fe0000003fc000000
def f472 : ℕ := 0x6419048c06832090d0c068007fffe0000ffffc01ffff
def f473 : ℕ := 0x40100800080201010000800001fe0000003fc000000
def f474 : ℕ := 0x1c4711c981c8e23939181c9ff801fe0000ffffffe0000
def f475 : ℕ := 0x441104880482209090804800001fe000000000000000
def f476 : ℕ := 0x2449124a824922494928249fffffffffff003fc000000
def f477 : ℕ := 0x441104880482209090804800000000000003fc000000
def f478 : ℕ := 0x22220f00
def f483 : ℕ := 0x140502820180a0503020180000000000000003fe0000
def f484 : ℕ := 0x1c8721d191c0e43a38191c1ff801fe0000ffffc000000
def f499 : ℕ := 0x140502820180a050302018000000001ff00000000000
def f500 : ℕ := 0x248922529241244a4829241ffffffffe00003fc000000
def f501 : ℕ := 0x401004080402008080804000000000000ffc00000000
def f502 : ℕ := 0x19c671b93198ce373313199ff801fe0000003fffe0000
def f503 : ℕ := 0x21c8723a32190e474323219ff801ffffff003fc000000
def f504 : ℕ := 0x1184613131108c2622131100000000000000000000000
def f505 : ℕ := 0x2008000804010000808040000001fe000000001fe00
def f506 : ℕ := 0xc4310c880c8621919080c9ff801fe0000ffffffe0000
def f507 : ℕ := 0x180603030100c0602030100000001fe0000000000000
def f508 : ℕ := 0x10240901090481202090904000000000000000001fe00
def f509 : ℕ := 0x5c17078b0582e0f0b0b059ff801fe0000003fc000000
def f510 : ℕ := 0x180601810180c030301018000000000000ffc03fe0000
def f511 : ℕ := 0x20080202020100404020200007fe01ffff00000000000
def f513 : ℕ := 0x1ff801fe000000000000000
def f514 : ℕ := 0x1dc771f9b1d8ee3f3b1b1d800000000000ffffffe0000
def f515 : ℕ := 0x22222f000f
def f520 : ℕ := 0x196659a9299ccb35339299dff8000001ffffc03fe01ff
def f521 : ℕ := 0x1e0781c1c1e0f0383c1c1e1ffffe000000ffc03ffffff
def f522 : ℕ := 0x19a669b13994cd363293995ff80001fe00ffc03fffe00
def f523 : ℕ := 0x380e03830381c0707030381fffffffffffffc03fe0000
def f525 : ℕ := 0x1ff800000000003fc000000
def f526 : ℕ := 0x44444f00f0
def f529 : ℕ := 0x21685a2a2a1d0b4543a2a1dffffe01ffff00003fe01ff
def f530 : ℕ := 0x26098242c26130484c2c261ffffe01ffffffc0001ffff
def f532 : ℕ := 0x11110f00
def f533 : ℕ := 0x31ac6b333b158d6662b3b15ffffe01ffff0000001fe00
def f534 : ℕ := 0x380e03830381c0707030381ffffe01ffffffffffe0000
def f535 : ℕ := 0x3fe01ff
def f536 : ℕ := 0x1605828281c0b05038281c000000001ff00000000000
def f537 : ℕ := 0x1e0781c1c1e0f0383c1c1e1ffffe000000ffffc01fe00
def f539 : ℕ := 0x401004080402008080804000000000000003fc000000
def f540 : ℕ := 0x1c0703830180e07030301800001fe000000000000000
def f541 : ℕ := 0x1a06818141a0d03034141a1ffffe000000ffc03ffffff
def f542 : ℕ := 0x10040101010080202010100000000000000000001fe00
def f543 : ℕ := 0x1fa7e9f1f9f4fd3e3e9f9f5ffffe01fe00fffffffffff
def f544 : ℕ := 0x1a0683038140d0602838140000001fe0000000000000
def f545 : ℕ := 0xe0380c0c0e070181c0c0e1ffffe000000ffffffe01ff
def f546 : ℕ := 0x1ffffe00000000000000000
def f547 : ℕ := 0x777fff
def f548 : ℕ := 0x3e0f83c3c3e1f0787c3c3e1ffffffffffffffffffffff
def f549 : ℕ := 0x1e0781c1c1e0f0383c1c1e000000000000fffffffffff
def f550 : ℕ := 0x33300f
def f551 : ℕ := 0x2008020202010040402020000001ffffff00000000000
def f552 : ℕ := 0x44440f00
def f553 : ℕ := 0x1ff000000001ff
def f554 : ℕ := 0x1605828281c0b05038281c0000000000000003fe0000
def f555 : ℕ := 0x66666fff00
def f556 : ℕ := 0x26098242c26130484c2c261ffffffffe00ffc0001fe00
def f557 : ℕ := 0x401004080402008080804000001fe000000000000000
def f558 : ℕ := 0x1c0703830180e07030301800000000000003fc000000
def f559 : ℕ := 0x22088202422110404424221ffffe01ffffffc0001ffff
def f563 : ℕ := 0x294a5294a5f83fff83e0
def f564 : ℕ := 0x1fe000000001fe00
def f565 : ℕ := 0x37adeb73fb75bd6e6ebfb75fffffffffffffc0001ffff
def f566 : ℕ := 0x11a4693139148d2622939140000000000000000000000
def f567 : ℕ := 0x26098242c26130484c2c261ffffffe01ffffc000001ff
def f570 : ℕ := 0x6318c6318cfffff07fe0
def f571 : ℕ := 0x1ff800000000ffc00000000
def f572 : ℕ := 0x180601810180c030301018000000000000003fffe0000
def f573 : ℕ := 0x26098242c26130484c2c260007ffffffff0000001ffff
def f574 : ℕ := 0x5550f0
def f576 : ℕ := 0x21685a2a2a1d0b4543a2a1dff801ffffff00003fe01ff
def f577 : ℕ := 0x25c9727ab2592e4f4b2b259ff801ffffff003fc000000
def f578 : ℕ := 0x31ac6b333b158d6662b3b15ff801ffffff0000001fe00
def f579 : ℕ := 0x20080202020100404020201ff801fe01ff00000000000
def f580 : ℕ := 0x666f0f
def f581 : ℕ := 0x380e03830381c0707030381ff801ffffffffffffe0000
def e0 : List ℕ := [f0,f1,f2,f3]
def e9 : List ℕ := [f12,f4,f11,f7]
def e12 : List ℕ := [f13,f4,f6,f7]
def e14 : List ℕ := [f13,f4,f11,f17]
def e16 : List ℕ := [f1,f2,f3]
def e17 : List ℕ := [f18,f19,f20,f21,f22,f23,f24]
def e19 : List ℕ := [f5,f6,f25,f7]
def e20 : List ℕ := [f8,f5,f6,f25,f7]
def e22 : List ℕ := [f5,f6,f27,f7]
def e23 : List ℕ := [f8,f5,f6,f27,f7]
def e27 : List ℕ := [f30,f13,f11,f7]
def e33 : List ℕ := [f40,f45,f42,f43,f44]
def e74 : List ℕ := [f14,f11,f7]
def e75 : List ℕ := [f75,f76,f21,f22,f23,f24]
def e76 : List ℕ := [f75,f20,f21,f22,f23,f24]
def e77 : List ℕ := [f75,f20,f76,f21,f22,f23,f24]
def e78 : List ℕ := [f77,f76,f21,f22,f23,f24]
def e79 : List ℕ := [f77,f20,f76,f21,f22,f23,f24]
def e80 : List ℕ := [f20,f76,f78,f22,f23,f24]
def e81 : List ℕ := [f20,f76,f21,f78,f22,f23,f24]
def e82 : List ℕ := [f79,f20,f76,f21,f22,f23,f24]
def e83 : List ℕ := [f80,f81]
def e89 : List ℕ := [f97,f98,f76,f22,f23,f24]
def e90 : List ℕ := [f98,f76,f99,f22,f23,f24]
def e91 : List ℕ := [f100,f98,f76,f22,f23,f24]
def e92 : List ℕ := [f98,f101,f76,f22,f23,f24]
def e93 : List ℕ := [f102,f98,f76,f22,f23,f24]
def e94 : List ℕ := [f76,f22,f103,f23,f24]
def e95 : List ℕ := [f98,f76,f22,f103,f23,f24]
def e96 : List ℕ := [f104,f76,f22,f23,f24]
def e97 : List ℕ := [f104,f98,f76,f22,f23,f24]
def e98 : List ℕ := [f98,f76,f105,f22,f23,f24]
def e99 : List ℕ := [f106,f98,f76,f22,f23,f24]
def e100 : List ℕ := [f98,f76,f22,f23,f107,f24]
def e101 : List ℕ := [f108,f98,f76,f22,f23,f24]
def e102 : List ℕ := [f98,f76,f22,f109,f23,f24]
def e103 : List ℕ := [f110,f98,f76,f22,f23,f24]
def e104 : List ℕ := [f98,f76,f22,f23,f24,f111]
def e105 : List ℕ := [f112,f98,f76,f22,f23,f24]
def e106 : List ℕ := [f98,f76,f22,f23,f113,f24]
def e107 : List ℕ := [f114,f98,f76,f22,f23,f24]
def e108 : List ℕ := [f98,f22,f115,f23,f24]
def e109 : List ℕ := [f98,f76,f115,f23,f24]
def e110 : List ℕ := [f98,f76,f22,f115,f23,f24]
def e111 : List ℕ := [f98,f116,f22,f23,f24]
def e112 : List ℕ := [f98,f116,f76,f22,f23,f24]
def e113 : List ℕ := [f98,f76,f117,f23,f24]
def e114 : List ℕ := [f98,f76,f117,f22,f23,f24]
def e115 : List ℕ := [f118,f98,f76,f22,f23,f24]
def e116 : List ℕ := [f98,f76,f22,f23,f119,f24]
def e117 : List ℕ := [f98,f120,f76,f22,f23,f24]
def e118 : List ℕ := [f98,f76,f22,f121,f23,f24]
def e119 : List ℕ := [f122,f98,f76,f22,f23,f24]
def e120 : List ℕ := [f98,f76,f22,f23,f24,f123]
def e121 : List ℕ := [f98,f124,f76,f22,f23,f24]
def e122 : List ℕ := [f98,f76,f22,f23,f125,f24]
def e123 : List ℕ := [f98,f76,f126,f22,f23,f24]
def e124 : List ℕ := [f33,f127,f37,f128]
def e126 : List ℕ := [f13,f4,f11,f7]
def e127 : List ℕ := [f98,f76,f23,f130,f24]
def e128 : List ℕ := [f98,f76,f22,f130,f24]
def e129 : List ℕ := [f98,f76,f22,f23,f130,f24]
def e130 : List ℕ := [f131,f98,f76,f23,f24]
def e131 : List ℕ := [f131,f98,f76,f22,f23,f24]
def e132 : List ℕ := [f98,f76,f132,f22,f24]
def e133 : List ℕ := [f98,f76,f132,f22,f23,f24]
def e134 : List ℕ := [f133,f98,f76,f22,f23,f24]
def e135 : List ℕ := [f98,f76,f22,f23,f134]
def e136 : List ℕ := [f98,f76,f22,f23,f24,f134]
def e137 : List ℕ := [f98,f76,f135,f22,f23,f24]
def e138 : List ℕ := [f98,f76,f22,f23,f136]
def e139 : List ℕ := [f98,f76,f22,f23,f136,f24]
def e140 : List ℕ := [f137,f98,f76,f22,f23,f24]
def e141 : List ℕ := [f98,f76,f22,f23,f24,f138]
def e142 : List ℕ := [f98,f76,f22,f139,f23,f24]
def e143 : List ℕ := [f98,f76,f22,f23,f140,f24]
def e144 : List ℕ := [f98,f76,f22,f23,f24]
def e145 : List ℕ := [f98,f76,f21,f22,f23,f24]
def e146 : List ℕ := [f98,f20,f76,f22,f23,f24]
def e147 : List ℕ := [f98,f20,f76,f21,f22,f23,f24]
def e148 : List ℕ := [f141,f20,f76,f21,f22,f23,f24]
def e155 : List ℕ := [f154,f76,f21,f155,f23,f24]
def e156 : List ℕ := [f76,f99,f155,f23,f24]
def e157 : List ℕ := [f76,f21,f99,f155,f23,f24]
def e158 : List ℕ := [f156,f76,f21,f155,f23,f24]
def e159 : List ℕ := [f100,f76,f155,f23,f24]
def e160 : List ℕ := [f100,f76,f21,f155,f23,f24]
def e161 : List ℕ := [f157,f76,f21,f155,f23,f24]
def e162 : List ℕ := [f76,f21,f155,f115,f23,f24]
def e163 : List ℕ := [f158,f76,f21,f155,f23,f24]
def e164 : List ℕ := [f76,f21,f117,f155,f23,f24]
def e165 : List ℕ := [f118,f76,f21,f155,f23,f24]
def e166 : List ℕ := [f76,f21,f155,f23,f119,f24]
def e167 : List ℕ := [f120,f76,f21,f155,f23,f24]
def e168 : List ℕ := [f76,f21,f155,f121,f23,f24]
def e169 : List ℕ := [f122,f76,f21,f155,f23,f24]
def e170 : List ℕ := [f76,f21,f155,f23,f24,f123]
def e171 : List ℕ := [f124,f76,f21,f155,f23,f24]
def e172 : List ℕ := [f76,f21,f155,f23,f125,f24]
def e173 : List ℕ := [f159,f76,f21,f155,f23,f24]
def e174 : List ℕ := [f76,f155,f160,f23,f24]
def e175 : List ℕ := [f76,f21,f155,f160,f23,f24]
def e176 : List ℕ := [f104,f76,f155,f23,f24]
def e177 : List ℕ := [f104,f76,f21,f155,f23,f24]
def e178 : List ℕ := [f76,f21,f161,f155,f23,f24]
def e179 : List ℕ := [f90,f91,f143,f144]
def e180 : List ℕ := [f106,f76,f21,f155,f23,f24]
def e181 : List ℕ := [f76,f21,f155,f23,f162,f24]
def e182 : List ℕ := [f76,f163,f21,f155,f23,f24]
def e183 : List ℕ := [f76,f21,f155,f109,f23,f24]
def e184 : List ℕ := [f110,f76,f21,f155,f23,f24]
def e185 : List ℕ := [f94,f95,f147,f149]
def e186 : List ℕ := [f76,f21,f155,f23,f24,f164]
def e187 : List ℕ := [f76,f165,f21,f155,f23,f24]
def e188 : List ℕ := [f76,f21,f155,f23,f113,f24]
def e189 : List ℕ := [f76,f21,f166,f155,f23,f24]
def e190 : List ℕ := [f76,f21,f23,f167,f24]
def e191 : List ℕ := [f76,f21,f155,f23,f167,f24]
def e192 : List ℕ := [f76,f168,f21,f23,f24]
def e193 : List ℕ := [f76,f168,f21,f155,f23,f24]
def e194 : List ℕ := [f76,f21,f169,f155,f23,f24]
def e195 : List ℕ := [f170,f76,f21,f155,f23,f24]
def e196 : List ℕ := [f76,f21,f155,f23,f24,f171]
def e197 : List ℕ := [f76,f21,f172,f155,f23,f24]
def e198 : List ℕ := [f76,f21,f155,f23,f173,f24]
def e199 : List ℕ := [f137,f76,f21,f155,f23,f24]
def e200 : List ℕ := [f76,f21,f155,f23,f24,f138]
def e201 : List ℕ := [f76,f21,f155,f139,f23,f24]
def e202 : List ℕ := [f76,f21,f155,f23,f140,f24]
def e203 : List ℕ := [f76,f21,f155,f23,f24]
def e204 : List ℕ := [f76,f21,f22,f155,f23,f24]
def e205 : List ℕ := [f20,f76,f21,f155,f23,f24]
def e206 : List ℕ := [f20,f76,f21,f22,f155,f23,f24]
def e207 : List ℕ := [f174,f76,f21,f22,f23,f24]
def e208 : List ℕ := [f174,f20,f76,f21,f22,f23,f24]
def e209 : List ℕ := [f20,f76,f21,f175,f23,f24]
def e210 : List ℕ := [f20,f76,f21,f175,f22,f23,f24]
def e211 : List ℕ := [f176,f20,f76,f21,f22,f23,f24]
def e212 : List ℕ := [f76,f21,f22,f23,f177,f24]
def e213 : List ℕ := [f20,f76,f21,f22,f23,f177,f24]
def e214 : List ℕ := [f178,f76,f21,f22,f23,f24]
def e215 : List ℕ := [f178,f20,f76,f21,f22,f23,f24]
def e216 : List ℕ := [f20,f76,f21,f22,f179,f23,f24]
def e217 : List ℕ := [f180,f20,f76,f21,f22,f23,f24]
def e225 : List ℕ := [f76,f99,f22,f23,f24,f189]
def e226 : List ℕ := [f100,f76,f22,f23,f24,f189]
def e227 : List ℕ := [f21,f22,f115,f23,f24,f189]
def e228 : List ℕ := [f76,f21,f115,f23,f24,f189]
def e229 : List ℕ := [f116,f21,f22,f23,f24,f189]
def e230 : List ℕ := [f76,f21,f117,f23,f24,f189]
def e231 : List ℕ := [f122,f76,f21,f22,f23,f189]
def e232 : List ℕ := [f124,f76,f21,f22,f23,f189]
def e233 : List ℕ := [f190,f76,f21,f22,f23,f24]
def e234 : List ℕ := [f191,f76,f21,f22,f23,f24]
def e235 : List ℕ := [f76,f22,f192,f23,f24,f189]
def e236 : List ℕ := [f76,f193,f22,f23,f24,f189]
def e237 : List ℕ := [f34,f143,f194,f195]
def e238 : List ℕ := [f76,f21,f22,f23,f189,f164]
def e239 : List ℕ := [f52,f60,f61,f74,f182]
def e240 : List ℕ := [f76,f21,f22,f23,f113,f189]
def e241 : List ℕ := [f196,f76,f21,f22,f23,f24]
def e242 : List ℕ := [f112,f76,f21,f22,f23,f24]
def e243 : List ℕ := [f33,f197,f37,f128]
def e244 : List ℕ := [f76,f21,f23,f130,f24,f189]
def e245 : List ℕ := [f76,f21,f22,f130,f24,f189]
def e246 : List ℕ := [f131,f76,f21,f23,f24,f189]
def e247 : List ℕ := [f76,f21,f132,f22,f24,f189]
def e248 : List ℕ := [f76,f21,f22,f23,f189,f134]
def e249 : List ℕ := [f76,f21,f22,f23,f136,f189]
def e250 : List ℕ := [f76,f21,f22,f23,f24,f171]
def e251 : List ℕ := [f76,f21,f22,f23,f24,f198]
def e252 : List ℕ := [f76,f21,f22,f23,f189,f138]
def e253 : List ℕ := [f14,f11,f199,f200]
def e254 : List ℕ := [f76,f21,f22,f23,f140,f189]
def e255 : List ℕ := [f76,f21,f22,f23,f24,f201]
def e256 : List ℕ := [f76,f21,f22,f23,f24,f202]
def e257 : List ℕ := [f203,f76,f21,f22,f23,f189]
def e258 : List ℕ := [f203,f76,f21,f22,f23,f24]
def e259 : List ℕ := [f76,f21,f22,f23,f24,f189]
def e260 : List ℕ := [f20,f76,f21,f22,f23,f24,f189]
def e261 : List ℕ := [f203,f20,f76,f21,f22,f23,f24]
def e262 : List ℕ := [f20,f76,f21,f22,f23,f204,f24]
def e263 : List ℕ := [f154,f20,f76,f21,f22,f23,f24]
def e264 : List ℕ := [f20,f76,f99,f22,f23,f24]
def e265 : List ℕ := [f20,f76,f21,f99,f22,f23,f24]
def e266 : List ℕ := [f156,f20,f76,f21,f22,f23,f24]
def e267 : List ℕ := [f100,f20,f76,f22,f23,f24]
def e268 : List ℕ := [f100,f20,f76,f21,f22,f23,f24]
def e269 : List ℕ := [f114,f20,f76,f21,f22,f23,f24]
def e270 : List ℕ := [f20,f21,f22,f115,f23,f24]
def e271 : List ℕ := [f20,f76,f21,f115,f23,f24]
def e272 : List ℕ := [f20,f76,f21,f22,f115,f23,f24]
def e273 : List ℕ := [f116,f20,f21,f22,f23,f24]
def e274 : List ℕ := [f116,f20,f76,f21,f22,f23,f24]
def e275 : List ℕ := [f20,f76,f21,f117,f23,f24]
def e276 : List ℕ := [f20,f76,f21,f117,f22,f23,f24]
def e277 : List ℕ := [f118,f20,f76,f21,f22,f23,f24]
def e278 : List ℕ := [f20,f76,f21,f22,f23,f119,f24]
def e279 : List ℕ := [f20,f120,f76,f21,f22,f23,f24]
def e280 : List ℕ := [f20,f76,f21,f22,f121,f23,f24]
def e281 : List ℕ := [f122,f20,f76,f21,f22,f23,f24]
def e282 : List ℕ := [f20,f76,f21,f22,f23,f24,f123]
def e283 : List ℕ := [f20,f124,f76,f21,f22,f23,f24]
def e284 : List ℕ := [f20,f76,f21,f22,f23,f125,f24]
def e285 : List ℕ := [f102,f20,f76,f21,f22,f23,f24]
def e286 : List ℕ := [f20,f76,f22,f192,f23,f24]
def e287 : List ℕ := [f20,f76,f21,f22,f192,f23,f24]
def e288 : List ℕ := [f20,f76,f193,f22,f23,f24]
def e289 : List ℕ := [f20,f76,f193,f21,f22,f23,f24]
def e290 : List ℕ := [f20,f76,f21,f105,f22,f23,f24]
def e291 : List ℕ := [f106,f20,f76,f21,f22,f23,f24]
def e292 : List ℕ := [f20,f76,f21,f22,f23,f162,f24]
def e293 : List ℕ := [f20,f76,f163,f21,f22,f23,f24]
def e294 : List ℕ := [f20,f76,f21,f22,f109,f23,f24]
def e296 : List ℕ := [f33,f37,f38]
def e297 : List ℕ := [f33,f197,f37,f38]
def e298 : List ℕ := [f110,f20,f76,f21,f22,f23,f24]
def e299 : List ℕ := [f8,f5,f6,f7]
def e304 : List ℕ := [f52,f62,f60,f61,f44]
def e305 : List ℕ := [f52,f62,f60,f61,f209]
def e306 : List ℕ := [f52,f62,f60,f61,f44,f209]
def e307 : List ℕ := [f20,f76,f21,f22,f23,f24,f164]
def e308 : List ℕ := [f210,f1,f2,f3]
def e309 : List ℕ := [f20,f76,f165,f21,f22,f23,f24]
def e310 : List ℕ := [f1,f2,f211,f3]
def e311 : List ℕ := [f20,f76,f21,f22,f23,f113,f24]
def e312 : List ℕ := [f20,f76,f21,f126,f22,f23,f24]
def e313 : List ℕ := [f20,f76,f21,f23,f130,f24]
def e314 : List ℕ := [f20,f76,f21,f22,f130,f24]
def e315 : List ℕ := [f20,f76,f21,f22,f23,f130,f24]
def e316 : List ℕ := [f131,f20,f76,f21,f23,f24]
def e317 : List ℕ := [f131,f20,f76,f21,f22,f23,f24]
def e318 : List ℕ := [f20,f76,f21,f132,f22,f24]
def e319 : List ℕ := [f20,f76,f21,f132,f22,f23,f24]
def e320 : List ℕ := [f133,f20,f76,f21,f22,f23,f24]
def e321 : List ℕ := [f20,f76,f21,f22,f23,f134]
def e322 : List ℕ := [f20,f76,f21,f22,f23,f24,f134]
def e323 : List ℕ := [f20,f76,f21,f135,f22,f23,f24]
def e324 : List ℕ := [f20,f76,f21,f22,f23,f136]
def e325 : List ℕ := [f20,f76,f21,f22,f23,f136,f24]
def e326 : List ℕ := [f137,f20,f76,f21,f22,f23,f24]
def e327 : List ℕ := [f20,f76,f21,f22,f23,f24,f138]
def e328 : List ℕ := [f20,f76,f21,f22,f139,f23,f24]
def e329 : List ℕ := [f20,f76,f21,f22,f23,f140,f24]
def e330 : List ℕ := [f20,f76,f21,f22,f23,f24]
def e332 : List ℕ := [f39,f52,f60,f61,f44]
def e333 : List ℕ := [f39,f40,f52,f60,f61,f44]
def e334 : List ℕ := [f40,f52,f60,f212,f61,f44]
def e335 : List ℕ := [f46,f40,f52,f60,f61,f44]
def e336 : List ℕ := [f213,f52,f60,f61,f44]
def e337 : List ℕ := [f40,f213,f52,f60,f61,f44]
def e338 : List ℕ := [f214,f52,f60,f61,f44]
def e339 : List ℕ := [f40,f214,f52,f61,f44]
def e340 : List ℕ := [f40,f214,f52,f60,f61,f44]
def e341 : List ℕ := [f48,f40,f52,f60,f61,f44]
def e342 : List ℕ := [f52,f60,f61,f215,f44]
def e343 : List ℕ := [f40,f52,f60,f61,f215,f44]
def e344 : List ℕ := [f216,f52,f60,f61,f44]
def e345 : List ℕ := [f216,f40,f52,f60,f61,f44]
def e346 : List ℕ := [f40,f52,f60,f217,f61,f44]
def e347 : List ℕ := [f218,f40,f52,f60,f61,f44]
def e348 : List ℕ := [f52,f60,f61,f44,f219]
def e349 : List ℕ := [f40,f52,f60,f61,f44,f219]
def e350 : List ℕ := [f220,f52,f60,f61,f44]
def e351 : List ℕ := [f220,f40,f52,f60,f61,f44]
def e352 : List ℕ := [f40,f52,f60,f61,f221,f44]
def e353 : List ℕ := [f40,f222,f52,f60,f61,f44]
def e354 : List ℕ := [f40,f52,f65,f61,f44]
def e355 : List ℕ := [f40,f52,f60,f65,f61,f44]
def e356 : List ℕ := [f66,f40,f52,f60,f61,f44]
def e357 : List ℕ := [f40,f223,f52,f61,f44]
def e358 : List ℕ := [f40,f223,f52,f60,f61,f44]
def e359 : List ℕ := [f68,f40,f52,f60,f61,f44]
def e360 : List ℕ := [f40,f52,f60,f224,f44]
def e361 : List ℕ := [f40,f52,f60,f61,f224,f44]
def e362 : List ℕ := [f40,f225,f52,f60,f61,f44]
def e363 : List ℕ := [f40,f52,f60,f71,f44]
def e364 : List ℕ := [f40,f52,f60,f71,f61,f44]
def e365 : List ℕ := [f72,f40,f52,f60,f61,f44]
def e366 : List ℕ := [f40,f52,f60,f61,f209]
def e367 : List ℕ := [f40,f52,f60,f61,f44,f209]
def e368 : List ℕ := [f40,f226,f52,f60,f61,f44]
def e369 : List ℕ := [f40,f52,f60,f61,f74]
def e370 : List ℕ := [f40,f52,f60,f61,f74,f44]
def e371 : List ℕ := [f227,f40,f52,f60,f61,f44]
def e372 : List ℕ := [f40,f52,f60,f61,f228,f44]
def e373 : List ℕ := [f40,f52,f229,f60,f61,f44]
def e374 : List ℕ := [f40,f52,f60,f230,f61,f44]
def e375 : List ℕ := [f231,f40,f52,f60,f61,f44]
def e376 : List ℕ := [f40,f52,f60,f61,f44,f232]
def e377 : List ℕ := [f40,f52,f233,f60,f61,f44]
def e378 : List ℕ := [f40,f52,f60,f61,f234,f44]
def e379 : List ℕ := [f235,f40,f52,f60,f61,f44]
def e380 : List ℕ := [f40,f52,f60,f61,f44,f186]
def e381 : List ℕ := [f40,f52,f60,f236,f61,f44]
def e382 : List ℕ := [f40,f52,f60,f61,f187,f44]
def e383 : List ℕ := [f40,f52,f60,f61,f44]
def e384 : List ℕ := [f19,f76,f21,f22,f23,f24]
def e385 : List ℕ := [f19,f20,f76,f21,f22,f23,f24]
def e435 : List ℕ := [f249,f250,f251,f256]
def e446 : List ℕ := [f97,f75,f20,f21,f22,f23,f24]
def e447 : List ℕ := [f75,f20,f260,f22,f23,f24]
def e448 : List ℕ := [f75,f20,f21,f260,f22,f23,f24]
def e449 : List ℕ := [f261,f75,f20,f21,f22,f23,f24]
def e450 : List ℕ := [f75,f20,f262,f22,f23,f24]
def e451 : List ℕ := [f75,f20,f262,f21,f22,f23,f24]
def e452 : List ℕ := [f263,f75,f20,f21,f22,f23,f24]
def e453 : List ℕ := [f20,f21,f22,f264,f23,f24]
def e454 : List ℕ := [f75,f20,f21,f264,f23,f24]
def e455 : List ℕ := [f75,f20,f21,f22,f264,f23,f24]
def e456 : List ℕ := [f158,f20,f21,f22,f23,f24]
def e457 : List ℕ := [f158,f75,f20,f21,f22,f23,f24]
def e458 : List ℕ := [f75,f20,f21,f265,f23,f24]
def e459 : List ℕ := [f75,f20,f21,f265,f22,f23,f24]
def e460 : List ℕ := [f266,f75,f20,f21,f22,f23,f24]
def e461 : List ℕ := [f75,f20,f21,f22,f267,f24]
def e462 : List ℕ := [f75,f20,f21,f22,f23,f267,f24]
def e463 : List ℕ := [f268,f75,f20,f21,f22,f23,f24]
def e464 : List ℕ := [f75,f20,f21,f22,f269,f24]
def e465 : List ℕ := [f75,f20,f21,f22,f269,f23,f24]
def e466 : List ℕ := [f270,f75,f20,f21,f22,f23,f24]
def e467 : List ℕ := [f75,f20,f21,f22,f23,f271]
def e468 : List ℕ := [f75,f20,f21,f22,f23,f24,f271]
def e469 : List ℕ := [f191,f75,f20,f21,f22,f23,f24]
def e470 : List ℕ := [f75,f20,f21,f22,f23,f272]
def e471 : List ℕ := [f75,f20,f21,f22,f23,f272,f24]
def e472 : List ℕ := [f75,f77,f20,f21,f22,f23,f24]
def e473 : List ℕ := [f75,f21,f78,f22,f23,f24]
def e474 : List ℕ := [f75,f20,f78,f22,f23,f24]
def e475 : List ℕ := [f75,f20,f21,f78,f22,f23,f24]
def e476 : List ℕ := [f75,f79,f21,f22,f23,f24]
def e477 : List ℕ := [f75,f79,f20,f21,f22,f23,f24]
def e478 : List ℕ := [f75,f98,f20,f22,f23,f24]
def e479 : List ℕ := [f75,f98,f20,f21,f22,f23,f24]
def e480 : List ℕ := [f75,f141,f20,f21,f22,f23,f24]
def e481 : List ℕ := [f75,f21,f22,f155,f23,f24]
def e482 : List ℕ := [f75,f20,f21,f155,f23,f24]
def e483 : List ℕ := [f75,f20,f21,f22,f155,f23,f24]
def e484 : List ℕ := [f75,f174,f21,f22,f23,f24]
def e485 : List ℕ := [f75,f174,f20,f21,f22,f23,f24]
def e486 : List ℕ := [f75,f20,f21,f175,f23,f24]
def e487 : List ℕ := [f75,f20,f21,f175,f22,f23,f24]
def e488 : List ℕ := [f176,f75,f20,f21,f22,f23,f24]
def e489 : List ℕ := [f75,f20,f21,f22,f23,f177,f24]
def e490 : List ℕ := [f75,f178,f20,f21,f22,f23,f24]
def e491 : List ℕ := [f75,f20,f21,f22,f179,f23,f24]
def e492 : List ℕ := [f180,f75,f20,f21,f22,f23,f24]
def e493 : List ℕ := [f75,f20,f21,f22,f23,f24,f189]
def e494 : List ℕ := [f75,f203,f20,f21,f22,f23,f24]
def e495 : List ℕ := [f75,f20,f21,f22,f23,f204,f24]
def e496 : List ℕ := [f102,f75,f20,f21,f22,f23,f24]
def e497 : List ℕ := [f75,f20,f22,f192,f23,f24]
def e498 : List ℕ := [f75,f20,f21,f22,f192,f23,f24]
def e499 : List ℕ := [f75,f20,f193,f22,f23,f24]
def e500 : List ℕ := [f75,f20,f193,f21,f22,f23,f24]
def e501 : List ℕ := [f75,f20,f21,f105,f22,f23,f24]
def e502 : List ℕ := [f106,f75,f20,f21,f22,f23,f24]
def e503 : List ℕ := [f75,f20,f21,f22,f23,f162,f24]
def e504 : List ℕ := [f75,f20,f163,f21,f22,f23,f24]
def e505 : List ℕ := [f75,f20,f21,f22,f109,f23,f24]
def e506 : List ℕ := [f110,f75,f20,f21,f22,f23,f24]
def e507 : List ℕ := [f75,f20,f21,f22,f23,f24,f164]
def e508 : List ℕ := [f75,f20,f165,f21,f22,f23,f24]
def e509 : List ℕ := [f75,f20,f21,f22,f23,f113,f24]
def e510 : List ℕ := [f75,f20,f21,f126,f22,f23,f24]
def e511 : List ℕ := [f75,f20,f21,f23,f130,f24]
def e512 : List ℕ := [f75,f20,f21,f22,f130,f24]
def e513 : List ℕ := [f75,f20,f21,f22,f23,f130,f24]
def e514 : List ℕ := [f75,f131,f20,f21,f23,f24]
def e515 : List ℕ := [f75,f131,f20,f21,f22,f23,f24]
def e516 : List ℕ := [f75,f20,f21,f132,f22,f24]
def e517 : List ℕ := [f75,f20,f21,f132,f22,f23,f24]
def e518 : List ℕ := [f133,f75,f20,f21,f22,f23,f24]
def e519 : List ℕ := [f75,f20,f21,f22,f23,f134]
def e520 : List ℕ := [f75,f20,f21,f22,f23,f24,f134]
def e521 : List ℕ := [f75,f20,f21,f135,f22,f23,f24]
def e522 : List ℕ := [f75,f20,f21,f22,f23,f136]
def e523 : List ℕ := [f75,f20,f21,f22,f23,f136,f24]
def e524 : List ℕ := [f137,f75,f20,f21,f22,f23,f24]
def e525 : List ℕ := [f75,f20,f21,f22,f23,f24,f138]
def e526 : List ℕ := [f75,f20,f21,f22,f139,f23,f24]
def e527 : List ℕ := [f75,f20,f21,f22,f23,f140,f24]
def e528 : List ℕ := [f75,f19,f20,f21,f22,f23,f24]
def e529 : List ℕ := [f39,f40,f214,f52,f61,f44]
def e530 : List ℕ := [f214,f52,f212,f61,f44]
def e531 : List ℕ := [f40,f214,f52,f212,f61,f44]
def e532 : List ℕ := [f46,f214,f52,f61,f44]
def e533 : List ℕ := [f46,f40,f214,f52,f61,f44]
def e534 : List ℕ := [f40,f214,f213,f52,f61,f44]
def e535 : List ℕ := [f48,f40,f214,f52,f61,f44]
def e536 : List ℕ := [f40,f214,f52,f61,f215,f44]
def e537 : List ℕ := [f216,f40,f214,f52,f61,f44]
def e538 : List ℕ := [f40,f214,f52,f217,f61,f44]
def e539 : List ℕ := [f218,f40,f214,f52,f61,f44]
def e540 : List ℕ := [f40,f214,f52,f61,f44,f219]
def e541 : List ℕ := [f220,f40,f214,f52,f61,f44]
def e542 : List ℕ := [f40,f214,f52,f61,f221,f44]
def e543 : List ℕ := [f40,f59,f214,f52,f61,f44]
def e544 : List ℕ := [f40,f273,f61,f44]
def e545 : List ℕ := [f40,f52,f273,f61,f44]
def e546 : List ℕ := [f40,f214,f273,f61,f44]
def e547 : List ℕ := [f40,f214,f52,f273,f61,f44]
def e548 : List ℕ := [f274,f40,f52,f61,f44]
def e549 : List ℕ := [f274,f40,f214,f52,f61,f44]
def e550 : List ℕ := [f64,f40,f214,f61,f44]
def e551 : List ℕ := [f64,f40,f214,f52,f61,f44]
def e552 : List ℕ := [f49,f40,f214,f52,f61,f44]
def e553 : List ℕ := [f40,f214,f52,f275,f44]
def e554 : List ℕ := [f40,f214,f52,f61,f275,f44]
def e555 : List ℕ := [f40,f276,f214,f52,f61,f44]
def e556 : List ℕ := [f40,f214,f52,f42,f44]
def e557 : List ℕ := [f40,f214,f52,f42,f61,f44]
def e558 : List ℕ := [f255,f40,f214,f52,f61,f44]
def e559 : List ℕ := [f40,f214,f52,f61,f277]
def e560 : List ℕ := [f40,f214,f52,f61,f44,f277]
def e561 : List ℕ := [f40,f278,f214,f52,f61,f44]
def e562 : List ℕ := [f40,f214,f52,f61,f279]
def e563 : List ℕ := [f40,f214,f52,f61,f279,f44]
def e564 : List ℕ := [f68,f40,f214,f52,f61,f44]
def e565 : List ℕ := [f40,f214,f52,f224,f44]
def e566 : List ℕ := [f40,f214,f52,f61,f224,f44]
def e567 : List ℕ := [f40,f214,f225,f52,f61,f44]
def e568 : List ℕ := [f40,f214,f52,f71,f44]
def e569 : List ℕ := [f40,f214,f52,f71,f61,f44]
def e570 : List ℕ := [f72,f40,f214,f52,f61,f44]
def e571 : List ℕ := [f40,f214,f52,f61,f209]
def e572 : List ℕ := [f40,f214,f52,f61,f44,f209]
def e573 : List ℕ := [f40,f214,f226,f52,f61,f44]
def e574 : List ℕ := [f40,f214,f52,f61,f74]
def e575 : List ℕ := [f40,f214,f52,f61,f74,f44]
def e576 : List ℕ := [f235,f40,f214,f52,f61,f44]
def e577 : List ℕ := [f40,f214,f52,f61,f44,f186]
def e578 : List ℕ := [f40,f214,f52,f236,f61,f44]
def e579 : List ℕ := [f40,f214,f52,f61,f187,f44]
def e580 : List ℕ := [f19,f280,f21,f22,f23,f24]
def e581 : List ℕ := [f19,f280,f20,f21,f22,f23,f24]
def e582 : List ℕ := [f97,f19,f20,f21,f22,f23,f24]
def e602 : List ℕ := [f18,f19,f20,f289,f22,f23,f24]
def e603 : List ℕ := [f20,f76,f289,f22,f23,f24]
def e604 : List ℕ := [f19,f20,f76,f289,f22,f23,f24]
def e605 : List ℕ := [f75,f20,f289,f22,f23,f24]
def e606 : List ℕ := [f75,f19,f20,f289,f22,f23,f24]
def e607 : List ℕ := [f19,f280,f20,f289,f22,f23,f24]
def e608 : List ℕ := [f81,f206,f290]
def e609 : List ℕ := [f20,f262,f289,f22,f23,f24]
def e610 : List ℕ := [f19,f20,f262,f22,f23,f24]
def e611 : List ℕ := [f19,f20,f262,f289,f22,f23,f24]
def e612 : List ℕ := [f291,f19,f20,f289,f22,f23,f24]
def e613 : List ℕ := [f19,f20,f289,f22,f292,f23,f24]
def e614 : List ℕ := [f293,f19,f20,f289,f22,f23,f24]
def e615 : List ℕ := [f19,f20,f289,f294,f22,f23,f24]
def e616 : List ℕ := [f266,f19,f20,f289,f22,f23,f24]
def e620 : List ℕ := [f297,f20,f289,f22,f298,f24]
def e621 : List ℕ := [f20,f289,f99,f22,f298,f24]
def e622 : List ℕ := [f299,f20,f289,f22,f298,f24]
def e623 : List ℕ := [f300,f20,f289,f22,f298,f24]
def e624 : List ℕ := [f141,f20,f289,f22,f298,f24]
def e625 : List ℕ := [f289,f22,f155,f298,f24]
def e626 : List ℕ := [f20,f289,f155,f298,f24]
def e627 : List ℕ := [f20,f289,f22,f155,f298,f24]
def e628 : List ℕ := [f174,f289,f22,f298,f24]
def e629 : List ℕ := [f174,f20,f289,f22,f298,f24]
def e630 : List ℕ := [f20,f289,f175,f298,f24]
def e631 : List ℕ := [f20,f289,f175,f22,f298,f24]
def e632 : List ℕ := [f301,f20,f289,f22,f298,f24]
def e633 : List ℕ := [f20,f289,f22,f119,f24]
def e634 : List ℕ := [f20,f289,f22,f298,f119,f24]
def e635 : List ℕ := [f302,f20,f289,f22,f298,f24]
def e636 : List ℕ := [f20,f289,f22,f303,f24]
def e637 : List ℕ := [f20,f289,f22,f303,f298,f24]
def e638 : List ℕ := [f180,f20,f289,f22,f298,f24]
def e639 : List ℕ := [f20,f289,f22,f298,f189]
def e640 : List ℕ := [f20,f289,f22,f298,f24,f189]
def e641 : List ℕ := [f203,f20,f289,f22,f298,f24]
def e642 : List ℕ := [f20,f289,f22,f298,f204]
def e643 : List ℕ := [f20,f289,f22,f298,f204,f24]
def e644 : List ℕ := [f304,f20,f289,f22,f298,f24]
def e645 : List ℕ := [f20,f22,f305,f298,f24]
def e646 : List ℕ := [f20,f289,f22,f305,f298,f24]
def e647 : List ℕ := [f20,f306,f22,f298,f24]
def e648 : List ℕ := [f20,f306,f289,f22,f298,f24]
def e649 : List ℕ := [f20,f289,f307,f22,f298,f24]
def e650 : List ℕ := [f13,f4,f281,f7]
def e651 : List ℕ := [f308,f20,f289,f22,f298,f24]
def e652 : List ℕ := [f20,f289,f22,f298,f309,f24]
def e653 : List ℕ := [f20,f310,f289,f22,f298,f24]
def e654 : List ℕ := [f20,f289,f22,f311,f298,f24]
def e655 : List ℕ := [f80,f81,f290]
def e656 : List ℕ := [f312,f20,f289,f22,f298,f24]
def e657 : List ℕ := [f13,f4,f281,f7,f313]
def e658 : List ℕ := [f20,f289,f22,f298,f24,f314]
def e659 : List ℕ := [f20,f315,f289,f22,f298,f24]
def e660 : List ℕ := [f20,f289,f22,f298,f316,f24]
def e661 : List ℕ := [f20,f289,f317,f22,f298,f24]
def e662 : List ℕ := [f20,f289,f22,f298,f318,f24]
def e663 : List ℕ := [f319,f20,f289,f22,f298,f24]
def e664 : List ℕ := [f20,f289,f320,f22,f298,f24]
def e665 : List ℕ := [f133,f20,f289,f22,f298,f24]
def e666 : List ℕ := [f20,f289,f22,f298,f134]
def e667 : List ℕ := [f20,f289,f22,f298,f24,f134]
def e668 : List ℕ := [f20,f289,f135,f22,f298,f24]
def e669 : List ℕ := [f20,f289,f22,f298,f136]
def e670 : List ℕ := [f20,f289,f22,f298,f136,f24]
def e671 : List ℕ := [f321,f20,f289,f22,f298,f24]
def e672 : List ℕ := [f20,f289,f22,f298,f24,f322]
def e673 : List ℕ := [f20,f289,f22,f323,f298,f24]
def e674 : List ℕ := [f20,f289,f22,f298,f324,f24]
def e675 : List ℕ := [f20,f289,f22,f298,f24]
def e676 : List ℕ := [f20,f289,f22,f23,f298,f24]
def e677 : List ℕ := [f19,f20,f289,f22,f298,f24]
def e678 : List ℕ := [f19,f20,f289,f22,f23,f298,f24]
def e679 : List ℕ := [f325,f20,f289,f22,f23,f24]
def e680 : List ℕ := [f325,f19,f20,f289,f22,f23,f24]
def e681 : List ℕ := [f19,f20,f289,f22,f269,f24]
def e682 : List ℕ := [f19,f20,f289,f22,f269,f23,f24]
def e683 : List ℕ := [f270,f19,f20,f289,f22,f23,f24]
def e712 : List ℕ := [f297,f20,f289,f22,f23,f342]
def e713 : List ℕ := [f20,f289,f99,f22,f23,f342]
def e714 : List ℕ := [f299,f20,f289,f22,f23,f342]
def e715 : List ℕ := [f300,f20,f289,f22,f23,f342]
def e716 : List ℕ := [f141,f20,f289,f22,f23,f342]
def e717 : List ℕ := [f289,f22,f155,f23,f342]
def e718 : List ℕ := [f20,f289,f155,f23,f342]
def e719 : List ℕ := [f20,f289,f22,f155,f23,f342]
def e720 : List ℕ := [f174,f289,f22,f23,f342]
def e721 : List ℕ := [f174,f20,f289,f22,f23,f342]
def e722 : List ℕ := [f20,f289,f175,f23,f342]
def e723 : List ℕ := [f20,f289,f175,f22,f23,f342]
def e724 : List ℕ := [f176,f20,f289,f22,f23,f342]
def e725 : List ℕ := [f20,f289,f22,f177,f342]
def e726 : List ℕ := [f4,f281,f327]
def e727 : List ℕ := [f20,f289,f22,f23,f177,f342]
def e728 : List ℕ := [f178,f20,f289,f22,f23,f342]
def e729 : List ℕ := [f20,f289,f22,f179,f342]
def e730 : List ℕ := [f20,f289,f22,f179,f23,f342]
def e731 : List ℕ := [f343,f20,f289,f22,f23,f342]
def e732 : List ℕ := [f20,f289,f22,f23,f123]
def e733 : List ℕ := [f20,f289,f22,f23,f342,f123]
def e734 : List ℕ := [f344,f20,f289,f22,f23,f342]
def e735 : List ℕ := [f20,f289,f22,f23,f345]
def e736 : List ℕ := [f20,f289,f22,f23,f345,f342]
def e737 : List ℕ := [f304,f20,f289,f22,f23,f342]
def e738 : List ℕ := [f20,f289,f22,f305,f23,f342]
def e739 : List ℕ := [f20,f306,f289,f22,f23,f342]
def e740 : List ℕ := [f20,f289,f307,f22,f23,f342]
def e741 : List ℕ := [f346,f20,f289,f22,f23,f342]
def e742 : List ℕ := [f20,f289,f22,f23,f309,f342]
def e743 : List ℕ := [f20,f347,f289,f22,f23,f342]
def e744 : List ℕ := [f20,f289,f22,f311,f23,f342]
def e745 : List ℕ := [f13,f4,f11,f327]
def e746 : List ℕ := [f348,f20,f289,f22,f23,f342]
def e747 : List ℕ := [f20,f289,f22,f23,f342,f314]
def e748 : List ℕ := [f20,f349,f289,f22,f23,f342]
def e749 : List ℕ := [f20,f289,f22,f23,f316,f342]
def e750 : List ℕ := [f20,f289,f126,f22,f23,f342]
def e751 : List ℕ := [f20,f289,f23,f130,f342]
def e752 : List ℕ := [f20,f289,f22,f130,f342]
def e753 : List ℕ := [f20,f289,f22,f23,f130,f342]
def e754 : List ℕ := [f131,f20,f289,f23,f342]
def e755 : List ℕ := [f131,f20,f289,f22,f23,f342]
def e756 : List ℕ := [f20,f289,f132,f22,f342]
def e757 : List ℕ := [f20,f289,f132,f22,f23,f342]
def e758 : List ℕ := [f350,f20,f289,f22,f23,f342]
def e759 : List ℕ := [f20,f289,f22,f23,f342,f351]
def e760 : List ℕ := [f20,f289,f352,f22,f23,f342]
def e761 : List ℕ := [f20,f289,f22,f23,f353,f342]
def e762 : List ℕ := [f354,f20,f289,f22,f23,f342]
def e763 : List ℕ := [f20,f289,f22,f23,f342,f322]
def e764 : List ℕ := [f20,f289,f22,f355,f23,f342]
def e765 : List ℕ := [f20,f289,f22,f23,f356,f342]
def e766 : List ℕ := [f20,f289,f22,f23,f342]
def e770 : List ℕ := [f20,f99,f22,f23,f24,f342]
def e771 : List ℕ := [f300,f20,f22,f23,f24,f342]
def e772 : List ℕ := [f289,f22,f155,f23,f24,f342]
def e773 : List ℕ := [f20,f289,f155,f23,f24,f342]
def e774 : List ℕ := [f174,f289,f22,f23,f24,f342]
def e775 : List ℕ := [f20,f289,f175,f23,f24,f342]
def e776 : List ℕ := [f20,f289,f22,f177,f24,f342]
def e777 : List ℕ := [f20,f289,f22,f179,f24,f342]
def e778 : List ℕ := [f180,f20,f289,f22,f23,f342]
def e779 : List ℕ := [f20,f289,f22,f23,f342,f189]
def e780 : List ℕ := [f203,f20,f289,f22,f23,f342]
def e781 : List ℕ := [f20,f289,f22,f23,f204,f342]
def e782 : List ℕ := [f20,f289,f22,f23,f24,f123]
def e783 : List ℕ := [f20,f289,f22,f23,f24,f345]
def e784 : List ℕ := [f20,f22,f305,f23,f24,f342]
def e785 : List ℕ := [f20,f306,f22,f23,f24,f342]
def e786 : List ℕ := [f312,f20,f289,f22,f23,f342]
def e787 : List ℕ := [f20,f315,f289,f22,f23,f342]
def e788 : List ℕ := [f348,f20,f289,f22,f23,f24]
def e789 : List ℕ := [f20,f349,f289,f22,f23,f24]
def e790 : List ℕ := [f20,f289,f23,f130,f24,f342]
def e791 : List ℕ := [f20,f289,f22,f130,f24,f342]
def e792 : List ℕ := [f131,f20,f289,f23,f24,f342]
def e793 : List ℕ := [f20,f289,f132,f22,f24,f342]
def e794 : List ℕ := [f133,f20,f289,f22,f23,f342]
def e795 : List ℕ := [f20,f289,f22,f23,f342,f134]
def e796 : List ℕ := [f20,f289,f135,f22,f23,f342]
def e797 : List ℕ := [f20,f289,f22,f23,f136,f342]
def e798 : List ℕ := [f137,f20,f289,f22,f23,f342]
def e799 : List ℕ := [f20,f289,f22,f23,f342,f138]
def e800 : List ℕ := [f20,f289,f22,f139,f23,f342]
def e801 : List ℕ := [f20,f289,f22,f23,f140,f342]
def e802 : List ℕ := [f20,f289,f22,f23,f24,f322]
def e803 : List ℕ := [f20,f289,f22,f23,f24,f356]
def e804 : List ℕ := [f358,f20,f289,f22,f23,f342]
def e805 : List ℕ := [f358,f20,f289,f22,f23,f24]
def e806 : List ℕ := [f20,f289,f22,f23,f24,f342]
def e807 : List ℕ := [f19,f20,f289,f22,f23,f342]
def e808 : List ℕ := [f19,f20,f289,f22,f23,f24,f342]
def e809 : List ℕ := [f358,f19,f20,f289,f22,f23,f24]
def e810 : List ℕ := [f19,f20,f289,f22,f23,f272]
def e811 : List ℕ := [f19,f20,f289,f22,f23,f272,f24]
def e812 : List ℕ := [f19,f297,f20,f289,f22,f23,f24]
def e813 : List ℕ := [f19,f20,f99,f22,f23,f24]
def e814 : List ℕ := [f19,f20,f289,f99,f22,f23,f24]
def e815 : List ℕ := [f299,f19,f20,f289,f22,f23,f24]
def e816 : List ℕ := [f19,f300,f20,f22,f23,f24]
def e817 : List ℕ := [f19,f300,f20,f289,f22,f23,f24]
def e818 : List ℕ := [f19,f141,f20,f289,f22,f23,f24]
def e819 : List ℕ := [f19,f289,f22,f155,f23,f24]
def e820 : List ℕ := [f19,f20,f289,f155,f23,f24]
def e821 : List ℕ := [f19,f20,f289,f22,f155,f23,f24]
def e822 : List ℕ := [f19,f174,f289,f22,f23,f24]
def e823 : List ℕ := [f19,f174,f20,f289,f22,f23,f24]
def e824 : List ℕ := [f19,f20,f289,f175,f23,f24]
def e825 : List ℕ := [f19,f20,f289,f175,f22,f23,f24]
def e826 : List ℕ := [f176,f19,f20,f289,f22,f23,f24]
def e827 : List ℕ := [f19,f20,f289,f22,f177,f24]
def e828 : List ℕ := [f19,f20,f289,f22,f23,f177,f24]
def e829 : List ℕ := [f19,f178,f20,f289,f22,f23,f24]
def e830 : List ℕ := [f19,f20,f289,f22,f179,f24]
def e831 : List ℕ := [f19,f20,f289,f22,f179,f23,f24]
def e832 : List ℕ := [f180,f19,f20,f289,f22,f23,f24]
def e833 : List ℕ := [f19,f20,f289,f22,f23,f189]
def e834 : List ℕ := [f19,f20,f289,f22,f23,f24,f189]
def e835 : List ℕ := [f19,f203,f20,f289,f22,f23,f24]
def e836 : List ℕ := [f19,f20,f289,f22,f23,f204]
def e837 : List ℕ := [f19,f20,f289,f22,f23,f204,f24]
def e838 : List ℕ := [f304,f19,f20,f289,f22,f23,f24]
def e839 : List ℕ := [f19,f20,f22,f305,f23,f24]
def e840 : List ℕ := [f19,f20,f289,f22,f305,f23,f24]
def e841 : List ℕ := [f19,f20,f306,f22,f23,f24]
def e842 : List ℕ := [f19,f20,f306,f289,f22,f23,f24]
def e843 : List ℕ := [f19,f20,f289,f307,f22,f23,f24]
def e844 : List ℕ := [f346,f19,f20,f289,f22,f23,f24]
def e845 : List ℕ := [f19,f20,f289,f22,f23,f309,f24]
def e846 : List ℕ := [f19,f20,f347,f289,f22,f23,f24]
def e847 : List ℕ := [f19,f20,f289,f22,f311,f23,f24]
def e848 : List ℕ := [f312,f19,f20,f289,f22,f23,f24]
def e849 : List ℕ := [f19,f20,f289,f22,f23,f24,f314]
def e850 : List ℕ := [f19,f20,f315,f289,f22,f23,f24]
def e851 : List ℕ := [f19,f20,f289,f22,f23,f316,f24]
def e852 : List ℕ := [f19,f20,f289,f126,f22,f23,f24]
def e853 : List ℕ := [f19,f20,f289,f23,f130,f24]
def e854 : List ℕ := [f19,f20,f289,f22,f130,f24]
def e855 : List ℕ := [f19,f20,f289,f22,f23,f130,f24]
def e856 : List ℕ := [f19,f131,f20,f289,f23,f24]
def e857 : List ℕ := [f19,f131,f20,f289,f22,f23,f24]
def e858 : List ℕ := [f19,f20,f289,f132,f22,f24]
def e859 : List ℕ := [f19,f20,f289,f132,f22,f23,f24]
def e860 : List ℕ := [f133,f19,f20,f289,f22,f23,f24]
def e861 : List ℕ := [f19,f20,f289,f22,f23,f134]
def e862 : List ℕ := [f19,f20,f289,f22,f23,f24,f134]
def e863 : List ℕ := [f19,f20,f289,f135,f22,f23,f24]
def e864 : List ℕ := [f19,f20,f289,f22,f23,f136]
def e865 : List ℕ := [f19,f20,f289,f22,f23,f136,f24]
def e866 : List ℕ := [f137,f19,f20,f289,f22,f23,f24]
def e867 : List ℕ := [f19,f20,f289,f22,f23,f24,f138]
def e868 : List ℕ := [f19,f20,f289,f22,f139,f23,f24]
def e869 : List ℕ := [f19,f20,f289,f22,f23,f140,f24]
def e870 : List ℕ := [f19,f20,f289,f22,f23,f24]
def e873 : List ℕ := [f20,f76,f21,f289,f22,f23,f24]
def e874 : List ℕ := [f19,f76,f21,f289,f22,f23,f24]
def e875 : List ℕ := [f75,f20,f21,f289,f22,f23,f24]
def e876 : List ℕ := [f19,f280,f21,f289,f22,f23,f24]
def e877 : List ℕ := [f97,f20,f21,f289,f22,f23,f24]
def e878 : List ℕ := [f97,f19,f20,f289,f22,f23,f24]
def e879 : List ℕ := [f361,f19,f20,f289,f22,f23,f24]
def e880 : List ℕ := [f20,f262,f21,f289,f22,f23,f24]
def e881 : List ℕ := [f19,f20,f262,f21,f22,f23,f24]
def e883 : List ℕ := [f41,f45,f42,f364,f44]
def e884 : List ℕ := [f20,f21,f289,f292,f23,f24]
def e885 : List ℕ := [f20,f21,f289,f22,f292,f23,f24]
def e886 : List ℕ := [f19,f20,f21,f289,f292,f23,f24]
def e887 : List ℕ := [f293,f20,f21,f289,f22,f23,f24]
def e888 : List ℕ := [f19,f20,f21,f289,f294,f23,f24]
def e889 : List ℕ := [f20,f21,f289,f22,f298,f24]
def e890 : List ℕ := [f13,f4,f11,f281,f7]
def e891 : List ℕ := [f20,f21,f289,f22,f23,f298,f24]
def e892 : List ℕ := [f19,f20,f21,f289,f22,f298,f24]
def e893 : List ℕ := [f325,f20,f21,f289,f22,f23,f24]
def e894 : List ℕ := [f19,f20,f21,f289,f22,f269,f24]
def e895 : List ℕ := [f20,f21,f289,f22,f23,f342]
def e896 : List ℕ := [f13,f4,f11,f7,f327]
def e897 : List ℕ := [f20,f21,f289,f22,f23,f24,f342]
def e898 : List ℕ := [f19,f20,f21,f289,f22,f23,f342]
def e899 : List ℕ := [f358,f20,f21,f289,f22,f23,f24]
def e900 : List ℕ := [f19,f20,f21,f289,f22,f23,f272]
def e901 : List ℕ := [f19,f77,f20,f289,f22,f23,f24]
def e902 : List ℕ := [f19,f21,f289,f78,f22,f23,f24]
def e903 : List ℕ := [f19,f20,f289,f78,f22,f23,f24]
def e904 : List ℕ := [f19,f79,f289,f22,f23,f24]
def e905 : List ℕ := [f19,f79,f21,f289,f22,f23,f24]
def e906 : List ℕ := [f19,f79,f20,f289,f22,f23,f24]
def e907 : List ℕ := [f19,f98,f20,f289,f22,f23,f24]
def e908 : List ℕ := [f19,f297,f20,f21,f22,f23,f24]
def e909 : List ℕ := [f248,f252,f250,f251,f365]
def e910 : List ℕ := [f19,f21,f99,f22,f23,f24]
def e911 : List ℕ := [f19,f21,f289,f99,f22,f23,f24]
def e912 : List ℕ := [f19,f20,f21,f99,f22,f23,f24]
def e913 : List ℕ := [f299,f19,f21,f22,f23,f24]
def e914 : List ℕ := [f299,f19,f21,f289,f22,f23,f24]
def e915 : List ℕ := [f299,f19,f20,f21,f22,f23,f24]
def e916 : List ℕ := [f19,f300,f20,f21,f22,f23,f24]
def e917 : List ℕ := [f19,f21,f289,f22,f155,f23,f24]
def e918 : List ℕ := [f19,f20,f21,f289,f155,f23,f24]
def e919 : List ℕ := [f19,f174,f21,f289,f22,f23,f24]
def e920 : List ℕ := [f19,f20,f21,f289,f175,f23,f24]
def e921 : List ℕ := [f19,f20,f21,f289,f22,f177,f24]
def e922 : List ℕ := [f19,f20,f21,f289,f22,f179,f24]
def e923 : List ℕ := [f19,f20,f21,f289,f22,f23,f189]
def e924 : List ℕ := [f19,f20,f21,f289,f22,f23,f204]
def e925 : List ℕ := [f361,f19,f20,f21,f22,f23,f24]
def e926 : List ℕ := [f102,f19,f20,f289,f22,f23,f24]
def e927 : List ℕ := [f19,f20,f289,f22,f192,f23,f24]
def e928 : List ℕ := [f19,f20,f193,f289,f22,f23,f24]
def e929 : List ℕ := [f19,f20,f289,f105,f22,f23,f24]
def e930 : List ℕ := [f106,f19,f20,f289,f22,f23,f24]
def e931 : List ℕ := [f19,f20,f289,f22,f23,f162,f24]
def e932 : List ℕ := [f19,f20,f163,f289,f22,f23,f24]
def e933 : List ℕ := [f19,f20,f289,f22,f109,f23,f24]
def e934 : List ℕ := [f110,f19,f20,f289,f22,f23,f24]
def e935 : List ℕ := [f13,f4,f11,f200]
def e936 : List ℕ := [f13,f4,f11,f7,f200]
def e937 : List ℕ := [f19,f20,f289,f22,f23,f24,f164]
def e938 : List ℕ := [f19,f20,f165,f289,f22,f23,f24]
def e939 : List ℕ := [f19,f20,f289,f22,f23,f113,f24]
def e940 : List ℕ := [f304,f19,f20,f21,f22,f23,f24]
def e941 : List ℕ := [f19,f20,f21,f22,f305,f23,f24]
def e942 : List ℕ := [f19,f20,f21,f306,f22,f23,f24]
def e943 : List ℕ := [f19,f20,f21,f307,f22,f23,f24]
def e944 : List ℕ := [f346,f19,f20,f21,f22,f23,f24]
def e945 : List ℕ := [f19,f20,f21,f22,f23,f309,f24]
def e946 : List ℕ := [f19,f20,f21,f347,f22,f23,f24]
def e947 : List ℕ := [f19,f20,f21,f22,f311,f23,f24]
def e948 : List ℕ := [f312,f19,f20,f21,f22,f23,f24]
def e949 : List ℕ := [f13,f4,f11,f7,f313]
def e950 : List ℕ := [f19,f20,f21,f22,f23,f24,f314]
def e951 : List ℕ := [f19,f20,f21,f315,f22,f23,f24]
def e952 : List ℕ := [f19,f20,f21,f22,f23,f316,f24]
def e953 : List ℕ := [f90,f91,f366,f144]
def e954 : List ℕ := [f19,f20,f21,f289,f23,f130,f24]
def e955 : List ℕ := [f19,f20,f21,f289,f22,f130,f24]
def e956 : List ℕ := [f19,f131,f20,f21,f289,f23,f24]
def e957 : List ℕ := [f19,f20,f21,f289,f132,f22,f24]
def e958 : List ℕ := [f19,f20,f21,f289,f22,f23,f134]
def e959 : List ℕ := [f19,f20,f21,f289,f22,f23,f136]
def e960 : List ℕ := [f19,f20,f21,f289,f22,f23,f24]
def e977 : List ℕ := [f18,f19,f20,f262,f22,f23,f24]
def e978 : List ℕ := [f20,f76,f262,f22,f23,f24]
def e979 : List ℕ := [f19,f20,f76,f262,f22,f23,f24]
def e980 : List ℕ := [f75,f19,f20,f262,f22,f23,f24]
def e981 : List ℕ := [f19,f280,f20,f262,f22,f23,f24]
def e982 : List ℕ := [f291,f19,f20,f262,f22,f23,f24]
def e983 : List ℕ := [f20,f262,f22,f292,f23,f24]
def e984 : List ℕ := [f19,f20,f262,f22,f292,f23,f24]
def e985 : List ℕ := [f293,f20,f262,f22,f23,f24]
def e986 : List ℕ := [f293,f19,f20,f262,f22,f23,f24]
def e987 : List ℕ := [f19,f20,f262,f294,f22,f23,f24]
def e988 : List ℕ := [f266,f19,f20,f262,f22,f23,f24]
def e989 : List ℕ := [f19,f20,f262,f22,f298,f24]
def e990 : List ℕ := [f19,f20,f262,f22,f23,f298,f24]
def e991 : List ℕ := [f325,f19,f20,f262,f22,f23,f24]
def e992 : List ℕ := [f19,f20,f262,f22,f269,f24]
def e993 : List ℕ := [f19,f20,f262,f22,f269,f23,f24]
def e994 : List ℕ := [f270,f19,f20,f262,f22,f23,f24]
def e995 : List ℕ := [f19,f20,f262,f22,f23,f342]
def e996 : List ℕ := [f19,f20,f262,f22,f23,f24,f342]
def e997 : List ℕ := [f358,f19,f20,f262,f22,f23,f24]
def e998 : List ℕ := [f19,f20,f262,f22,f23,f272]
def e999 : List ℕ := [f19,f20,f262,f22,f23,f272,f24]
def e1000 : List ℕ := [f19,f77,f20,f262,f22,f23,f24]
def e1001 : List ℕ := [f19,f262,f371,f22,f23,f24]
def e1002 : List ℕ := [f19,f20,f371,f22,f23,f24]
def e1003 : List ℕ := [f19,f20,f262,f371,f22,f23,f24]
def e1004 : List ℕ := [f19,f79,f262,f22,f23,f24]
def e1005 : List ℕ := [f19,f79,f20,f262,f22,f23,f24]
def e1006 : List ℕ := [f19,f100,f20,f22,f23,f24]
def e1007 : List ℕ := [f19,f100,f20,f262,f22,f23,f24]
def e1008 : List ℕ := [f19,f141,f20,f262,f22,f23,f24]
def e1009 : List ℕ := [f19,f262,f22,f155,f23,f24]
def e1010 : List ℕ := [f19,f20,f262,f155,f23,f24]
def e1011 : List ℕ := [f19,f20,f262,f22,f155,f23,f24]
def e1012 : List ℕ := [f19,f174,f262,f22,f23,f24]
def e1013 : List ℕ := [f19,f174,f20,f262,f22,f23,f24]
def e1014 : List ℕ := [f19,f20,f262,f175,f23,f24]
def e1015 : List ℕ := [f19,f20,f262,f175,f22,f23,f24]
def e1016 : List ℕ := [f176,f19,f20,f262,f22,f23,f24]
def e1017 : List ℕ := [f19,f20,f262,f22,f177,f24]
def e1018 : List ℕ := [f19,f20,f262,f22,f23,f177,f24]
def e1019 : List ℕ := [f19,f178,f20,f262,f22,f23,f24]
def e1020 : List ℕ := [f19,f20,f262,f22,f179,f24]
def e1021 : List ℕ := [f19,f20,f262,f22,f179,f23,f24]
def e1022 : List ℕ := [f180,f19,f20,f262,f22,f23,f24]
def e1023 : List ℕ := [f19,f20,f262,f22,f23,f189]
def e1024 : List ℕ := [f19,f20,f262,f22,f23,f24,f189]
def e1025 : List ℕ := [f19,f203,f20,f262,f22,f23,f24]
def e1026 : List ℕ := [f19,f20,f262,f22,f23,f204]
def e1027 : List ℕ := [f19,f20,f262,f22,f23,f204,f24]
def e1028 : List ℕ := [f102,f19,f20,f262,f22,f23,f24]
def e1029 : List ℕ := [f19,f20,f22,f372,f23,f24]
def e1030 : List ℕ := [f19,f20,f262,f22,f372,f23,f24]
def e1031 : List ℕ := [f19,f20,f373,f22,f23,f24]
def e1032 : List ℕ := [f19,f20,f373,f262,f22,f23,f24]
def e1033 : List ℕ := [f19,f20,f262,f105,f22,f23,f24]
def e1034 : List ℕ := [f106,f19,f20,f262,f22,f23,f24]
def e1035 : List ℕ := [f19,f20,f262,f22,f23,f374,f24]
def e1036 : List ℕ := [f19,f20,f310,f262,f22,f23,f24]
def e1037 : List ℕ := [f19,f20,f262,f22,f109,f23,f24]
def e1038 : List ℕ := [f110,f19,f20,f262,f22,f23,f24]
def e1039 : List ℕ := [f19,f20,f262,f22,f23,f24,f375]
def e1040 : List ℕ := [f19,f20,f349,f262,f22,f23,f24]
def e1041 : List ℕ := [f19,f20,f262,f22,f23,f113,f24]
def e1042 : List ℕ := [f19,f20,f262,f126,f22,f23,f24]
def e1051 : List ℕ := [f19,f20,f262,f23,f130,f24]
def e1052 : List ℕ := [f19,f20,f262,f22,f130,f24]
def e1053 : List ℕ := [f19,f20,f262,f22,f23,f130,f24]
def e1054 : List ℕ := [f19,f131,f20,f262,f23,f24]
def e1055 : List ℕ := [f19,f131,f20,f262,f22,f23,f24]
def e1056 : List ℕ := [f19,f20,f262,f132,f22,f24]
def e1057 : List ℕ := [f19,f20,f262,f132,f22,f23,f24]
def e1058 : List ℕ := [f133,f19,f20,f262,f22,f23,f24]
def e1059 : List ℕ := [f19,f20,f262,f22,f23,f134]
def e1060 : List ℕ := [f19,f20,f262,f22,f23,f24,f134]
def e1061 : List ℕ := [f19,f20,f262,f135,f22,f23,f24]
def e1062 : List ℕ := [f19,f20,f262,f22,f23,f136]
def e1063 : List ℕ := [f19,f20,f262,f22,f23,f136,f24]
def e1064 : List ℕ := [f137,f19,f20,f262,f22,f23,f24]
def e1065 : List ℕ := [f19,f20,f262,f22,f23,f24,f138]
def e1066 : List ℕ := [f19,f20,f262,f22,f139,f23,f24]
def e1067 : List ℕ := [f19,f20,f262,f22,f23,f140,f24]
def e1068 : List ℕ := [f291,f19,f20,f21,f22,f23,f24]
def e1069 : List ℕ := [f20,f21,f22,f292,f23,f24]
def e1070 : List ℕ := [f19,f20,f21,f292,f23,f24]
def e1071 : List ℕ := [f19,f20,f21,f22,f292,f23,f24]
def e1072 : List ℕ := [f293,f20,f21,f22,f23,f24]
def e1073 : List ℕ := [f293,f19,f20,f21,f22,f23,f24]
def e1074 : List ℕ := [f19,f20,f21,f294,f23,f24]
def e1075 : List ℕ := [f19,f20,f21,f294,f22,f23,f24]
def e1076 : List ℕ := [f266,f19,f20,f21,f22,f23,f24]
def e1077 : List ℕ := [f19,f20,f21,f22,f298,f24]
def e1078 : List ℕ := [f19,f20,f21,f22,f23,f298,f24]
def e1079 : List ℕ := [f325,f19,f20,f21,f22,f23,f24]
def e1080 : List ℕ := [f19,f20,f21,f22,f269,f24]
def e1081 : List ℕ := [f19,f20,f21,f22,f269,f23,f24]
def e1082 : List ℕ := [f270,f19,f20,f21,f22,f23,f24]
def e1086 : List ℕ := [f18,f19,f20,f21,f22,f23,f342]
def e1087 : List ℕ := [f19,f20,f76,f21,f22,f23,f342]
def e1088 : List ℕ := [f75,f19,f20,f21,f22,f23,f342]
def e1089 : List ℕ := [f19,f280,f20,f21,f22,f23,f342]
def e1090 : List ℕ := [f97,f19,f20,f21,f22,f23,f342]
def e1091 : List ℕ := [f361,f20,f21,f22,f23,f342]
def e1092 : List ℕ := [f361,f19,f20,f21,f22,f23,f342]
def e1093 : List ℕ := [f19,f20,f262,f21,f22,f23,f342]
def e1094 : List ℕ := [f291,f19,f20,f21,f22,f23,f342]
def e1095 : List ℕ := [f19,f20,f21,f22,f292,f23,f342]
def e1096 : List ℕ := [f293,f19,f20,f21,f22,f23,f342]
def e1097 : List ℕ := [f19,f20,f21,f294,f22,f23,f342]
def e1098 : List ℕ := [f266,f19,f20,f21,f22,f23,f342]
def e1099 : List ℕ := [f20,f21,f22,f298,f342]
def e1100 : List ℕ := [f20,f21,f22,f23,f298,f342]
def e1101 : List ℕ := [f19,f20,f21,f22,f298,f342]
def e1102 : List ℕ := [f19,f20,f21,f22,f23,f298,f342]
def e1103 : List ℕ := [f325,f20,f21,f22,f23,f342]
def e1104 : List ℕ := [f325,f19,f20,f21,f22,f23,f342]
def e1105 : List ℕ := [f19,f20,f21,f22,f269,f342]
def e1106 : List ℕ := [f19,f20,f21,f22,f269,f23,f342]
def e1107 : List ℕ := [f20,f21,f22,f23,f272,f342]
def e1108 : List ℕ := [f19,f20,f21,f22,f23,f272]
def e1109 : List ℕ := [f19,f20,f21,f22,f23,f272,f342]
def e1110 : List ℕ := [f19,f77,f20,f21,f22,f23,f342]
def e1111 : List ℕ := [f33,f34,f379,f380]
def e1112 : List ℕ := [f19,f21,f78,f22,f23,f342]
def e1113 : List ℕ := [f19,f20,f78,f22,f23,f342]
def e1114 : List ℕ := [f19,f20,f21,f78,f22,f23,f342]
def e1115 : List ℕ := [f19,f79,f21,f22,f23,f342]
def e1116 : List ℕ := [f19,f79,f20,f21,f22,f23,f342]
def e1117 : List ℕ := [f19,f98,f20,f22,f23,f342]
def e1118 : List ℕ := [f19,f98,f20,f21,f22,f23,f342]
def e1119 : List ℕ := [f19,f141,f20,f21,f22,f23,f342]
def e1120 : List ℕ := [f19,f21,f22,f155,f23,f342]
def e1121 : List ℕ := [f19,f20,f21,f155,f23,f342]
def e1122 : List ℕ := [f19,f20,f21,f22,f155,f23,f342]
def e1123 : List ℕ := [f19,f174,f21,f22,f23,f342]
def e1124 : List ℕ := [f19,f174,f20,f21,f22,f23,f342]
def e1125 : List ℕ := [f19,f20,f21,f175,f23,f342]
def e1126 : List ℕ := [f19,f20,f21,f175,f22,f23,f342]
def e1127 : List ℕ := [f176,f19,f20,f21,f22,f23,f342]
def e1128 : List ℕ := [f19,f20,f21,f22,f177,f342]
def e1129 : List ℕ := [f19,f20,f21,f22,f23,f177,f342]
def e1130 : List ℕ := [f19,f178,f20,f21,f22,f23,f342]
def e1131 : List ℕ := [f19,f20,f21,f22,f179,f342]
def e1132 : List ℕ := [f19,f20,f21,f22,f179,f23,f342]
def e1133 : List ℕ := [f343,f19,f20,f21,f22,f23,f342]
def e1134 : List ℕ := [f19,f20,f21,f22,f23,f123]
def e1135 : List ℕ := [f19,f20,f21,f22,f23,f342,f123]
def e1136 : List ℕ := [f19,f344,f20,f21,f22,f23,f342]
def e1137 : List ℕ := [f19,f20,f21,f22,f23,f345]
def e1138 : List ℕ := [f19,f20,f21,f22,f23,f345,f342]
def e1139 : List ℕ := [f102,f19,f20,f21,f22,f23,f342]
def e1140 : List ℕ := [f19,f20,f22,f192,f23,f342]
def e1141 : List ℕ := [f19,f20,f21,f22,f192,f23,f342]
def e1142 : List ℕ := [f19,f20,f193,f22,f23,f342]
def e1143 : List ℕ := [f19,f20,f193,f21,f22,f23,f342]
def e1144 : List ℕ := [f19,f20,f21,f105,f22,f23,f342]
def e1145 : List ℕ := [f106,f19,f20,f21,f22,f23,f342]
def e1146 : List ℕ := [f19,f20,f21,f22,f23,f162,f342]
def e1147 : List ℕ := [f19,f20,f163,f21,f22,f23,f342]
def e1148 : List ℕ := [f19,f20,f21,f22,f109,f23,f342]
def e1149 : List ℕ := [f381,f19,f20,f21,f22,f23,f342]
def e1150 : List ℕ := [f19,f20,f21,f22,f23,f342,f314]
def e1151 : List ℕ := [f19,f20,f349,f21,f22,f23,f342]
def e1152 : List ℕ := [f19,f20,f21,f22,f23,f382,f342]
def e1153 : List ℕ := [f19,f20,f21,f126,f22,f23,f342]
def e1154 : List ℕ := [f19,f20,f21,f23,f130,f342]
def e1155 : List ℕ := [f19,f20,f21,f22,f130,f342]
def e1156 : List ℕ := [f19,f20,f21,f22,f23,f130,f342]
def e1157 : List ℕ := [f19,f131,f20,f21,f23,f342]
def e1158 : List ℕ := [f19,f131,f20,f21,f22,f23,f342]
def e1159 : List ℕ := [f19,f20,f21,f132,f22,f342]
def e1160 : List ℕ := [f19,f20,f21,f132,f22,f23,f342]
def e1161 : List ℕ := [f350,f19,f20,f21,f22,f23,f342]
def e1162 : List ℕ := [f19,f20,f21,f22,f23,f351]
def e1163 : List ℕ := [f19,f20,f21,f22,f23,f342,f351]
def e1164 : List ℕ := [f19,f20,f21,f352,f22,f23,f342]
def e1165 : List ℕ := [f19,f20,f21,f22,f23,f353]
def e1166 : List ℕ := [f19,f20,f21,f22,f23,f353,f342]
def e1167 : List ℕ := [f354,f19,f20,f21,f22,f23,f342]
def e1168 : List ℕ := [f19,f20,f21,f22,f23,f342,f322]
def e1169 : List ℕ := [f19,f20,f21,f22,f355,f23,f342]
def e1170 : List ℕ := [f19,f20,f21,f22,f23,f356,f342]
def e1171 : List ℕ := [f19,f20,f21,f22,f23,f342]
def e1172 : List ℕ := [f76,f21,f22,f23,f24,f342]
def e1173 : List ℕ := [f20,f76,f21,f22,f23,f24,f342]
def e1174 : List ℕ := [f19,f76,f21,f22,f23,f24,f342]
def e1175 : List ℕ := [f75,f20,f21,f22,f23,f24,f342]
def e1176 : List ℕ := [f19,f280,f21,f22,f23,f24,f342]
def e1177 : List ℕ := [f361,f20,f21,f22,f23,f24,f342]
def e1178 : List ℕ := [f20,f21,f292,f23,f24,f342]
def e1179 : List ℕ := [f20,f21,f22,f292,f23,f24,f342]
def e1180 : List ℕ := [f19,f20,f21,f292,f23,f24,f342]
def e1181 : List ℕ := [f293,f20,f21,f22,f23,f24,f342]
def e1182 : List ℕ := [f19,f20,f21,f294,f23,f24,f342]
def e1183 : List ℕ := [f20,f21,f22,f298,f24,f342]
def e1184 : List ℕ := [f20,f21,f22,f23,f298,f24,f342]
def e1185 : List ℕ := [f19,f20,f21,f22,f298,f24,f342]
def e1186 : List ℕ := [f325,f20,f21,f22,f23,f24,f342]
def e1187 : List ℕ := [f19,f20,f21,f22,f269,f24,f342]
def e1188 : List ℕ := [f270,f20,f21,f22,f23,f24,f342]
def e1189 : List ℕ := [f270,f19,f20,f21,f22,f23,f342]
def e1190 : List ℕ := [f358,f19,f20,f21,f22,f23,f342]
def e1191 : List ℕ := [f20,f21,f22,f23,f272,f24,f342]
def e1192 : List ℕ := [f19,f20,f21,f22,f23,f272,f24]
def e1193 : List ℕ := [f19,f21,f78,f22,f23,f24,f342]
def e1194 : List ℕ := [f19,f20,f78,f22,f23,f24,f342]
def e1195 : List ℕ := [f19,f79,f21,f22,f23,f24,f342]
def e1196 : List ℕ := [f19,f98,f20,f22,f23,f24,f342]
def e1197 : List ℕ := [f19,f21,f22,f155,f23,f24,f342]
def e1198 : List ℕ := [f19,f20,f21,f155,f23,f24,f342]
def e1199 : List ℕ := [f19,f174,f21,f22,f23,f24,f342]
def e1200 : List ℕ := [f19,f20,f21,f175,f23,f24,f342]
def e1201 : List ℕ := [f19,f20,f21,f22,f177,f24,f342]
def e1202 : List ℕ := [f19,f20,f21,f22,f179,f24,f342]
def e1203 : List ℕ := [f180,f19,f20,f21,f22,f23,f342]
def e1204 : List ℕ := [f19,f20,f21,f22,f23,f342,f189]
def e1205 : List ℕ := [f19,f203,f20,f21,f22,f23,f342]
def e1206 : List ℕ := [f19,f20,f21,f22,f23,f204,f342]
def e1207 : List ℕ := [f343,f19,f20,f21,f22,f23,f24]
def e1208 : List ℕ := [f19,f20,f21,f22,f23,f24,f123]
def e1209 : List ℕ := [f19,f344,f20,f21,f22,f23,f24]
def e1210 : List ℕ := [f19,f20,f21,f22,f23,f24,f345]
def e1211 : List ℕ := [f19,f20,f22,f192,f23,f24,f342]
def e1212 : List ℕ := [f19,f20,f193,f22,f23,f24,f342]
def e1213 : List ℕ := [f110,f19,f20,f21,f22,f23,f342]
def e1214 : List ℕ := [f19,f20,f21,f22,f23,f342,f164]
def e1215 : List ℕ := [f19,f20,f165,f21,f22,f23,f342]
def e1216 : List ℕ := [f19,f20,f21,f22,f23,f113,f342]
def e1217 : List ℕ := [f381,f19,f20,f21,f22,f23,f24]
def e1218 : List ℕ := [f19,f20,f349,f21,f22,f23,f24]
def e1219 : List ℕ := [f19,f20,f21,f22,f23,f24,f382]
def e1220 : List ℕ := [f19,f20,f21,f23,f130,f24,f342]
def e1221 : List ℕ := [f19,f20,f21,f22,f130,f24,f342]
def e1222 : List ℕ := [f19,f131,f20,f21,f23,f24,f342]
def e1223 : List ℕ := [f19,f20,f21,f132,f22,f24,f342]
def e1224 : List ℕ := [f133,f19,f20,f21,f22,f23,f342]
def e1225 : List ℕ := [f19,f20,f21,f22,f23,f342,f134]
def e1226 : List ℕ := [f19,f20,f21,f135,f22,f23,f342]
def e1227 : List ℕ := [f19,f20,f21,f22,f23,f136,f342]
def e1228 : List ℕ := [f350,f19,f20,f21,f22,f23,f24]
def e1229 : List ℕ := [f19,f20,f21,f22,f23,f24,f351]
def e1230 : List ℕ := [f19,f20,f21,f352,f22,f23,f24]
def e1231 : List ℕ := [f19,f20,f21,f22,f23,f24,f353]
def e1232 : List ℕ := [f137,f19,f20,f21,f22,f23,f342]
def e1233 : List ℕ := [f19,f20,f21,f22,f23,f342,f138]
def e1234 : List ℕ := [f19,f20,f21,f22,f139,f23,f342]
def e1235 : List ℕ := [f19,f20,f21,f22,f23,f140,f342]
def e1236 : List ℕ := [f354,f19,f20,f21,f22,f23,f24]
def e1237 : List ℕ := [f19,f20,f21,f22,f23,f24,f322]
def e1238 : List ℕ := [f19,f20,f21,f22,f355,f23,f24]
def e1239 : List ℕ := [f19,f20,f21,f22,f23,f24,f356]
def e1240 : List ℕ := [f358,f19,f20,f21,f22,f23,f24]
def e1241 : List ℕ := [f19,f20,f21,f22,f23,f24,f342]
def e1268 : List ℕ := [f18,f19,f20,f21,f22,f23,f272]
def e1269 : List ℕ := [f20,f76,f21,f22,f23,f272]
def e1270 : List ℕ := [f19,f20,f76,f21,f22,f23,f272]
def e1271 : List ℕ := [f75,f19,f20,f21,f22,f23,f272]
def e1272 : List ℕ := [f19,f280,f20,f21,f22,f23,f272]
def e1273 : List ℕ := [f97,f19,f20,f21,f22,f23,f272]
def e1274 : List ℕ := [f361,f19,f20,f21,f22,f23,f272]
def e1275 : List ℕ := [f19,f20,f262,f21,f22,f23,f272]
def e1276 : List ℕ := [f291,f19,f20,f21,f22,f23,f272]
def e1277 : List ℕ := [f20,f21,f22,f292,f23,f272]
def e1278 : List ℕ := [f19,f20,f21,f22,f292,f23,f272]
def e1279 : List ℕ := [f293,f20,f21,f22,f23,f272]
def e1280 : List ℕ := [f293,f19,f20,f21,f22,f23,f272]
def e1281 : List ℕ := [f19,f20,f21,f294,f22,f23,f272]
def e1282 : List ℕ := [f266,f19,f20,f21,f22,f23,f272]
def e1283 : List ℕ := [f19,f20,f21,f22,f298,f272]
def e1284 : List ℕ := [f19,f20,f21,f22,f23,f298,f272]
def e1285 : List ℕ := [f325,f19,f20,f21,f22,f23,f272]
def e1286 : List ℕ := [f19,f20,f21,f22,f269,f272]
def e1287 : List ℕ := [f19,f20,f21,f22,f269,f23,f272]
def e1288 : List ℕ := [f19,f77,f20,f21,f22,f23,f272]
def e1292 : List ℕ := [f19,f21,f78,f22,f23,f272]
def e1293 : List ℕ := [f19,f20,f78,f22,f23,f272]
def e1294 : List ℕ := [f19,f20,f21,f78,f22,f23,f272]
def e1295 : List ℕ := [f19,f79,f21,f22,f23,f272]
def e1296 : List ℕ := [f19,f79,f20,f21,f22,f23,f272]
def e1297 : List ℕ := [f19,f98,f20,f22,f23,f272]
def e1298 : List ℕ := [f19,f98,f20,f21,f22,f23,f272]
def e1299 : List ℕ := [f19,f141,f20,f21,f22,f23,f272]
def e1300 : List ℕ := [f19,f21,f22,f155,f23,f272]
def e1301 : List ℕ := [f19,f20,f21,f155,f23,f272]
def e1302 : List ℕ := [f19,f20,f21,f22,f155,f23,f272]
def e1303 : List ℕ := [f19,f174,f21,f22,f23,f272]
def e1304 : List ℕ := [f19,f174,f20,f21,f22,f23,f272]
def e1305 : List ℕ := [f19,f20,f21,f175,f23,f272]
def e1306 : List ℕ := [f19,f20,f21,f175,f22,f23,f272]
def e1307 : List ℕ := [f176,f19,f20,f21,f22,f23,f272]
def e1308 : List ℕ := [f19,f20,f21,f22,f177,f272]
def e1309 : List ℕ := [f19,f20,f21,f22,f23,f177,f272]
def e1310 : List ℕ := [f19,f178,f20,f21,f22,f23,f272]
def e1311 : List ℕ := [f19,f20,f21,f22,f179,f272]
def e1312 : List ℕ := [f19,f20,f21,f22,f179,f23,f272]
def e1313 : List ℕ := [f180,f19,f20,f21,f22,f23,f272]
def e1314 : List ℕ := [f19,f20,f21,f22,f23,f386]
def e1315 : List ℕ := [f19,f20,f21,f22,f23,f272,f386]
def e1316 : List ℕ := [f19,f203,f20,f21,f22,f23,f272]
def e1317 : List ℕ := [f19,f20,f21,f22,f23,f125]
def e1318 : List ℕ := [f19,f20,f21,f22,f23,f125,f272]
def e1319 : List ℕ := [f102,f19,f20,f21,f22,f23,f272]
def e1320 : List ℕ := [f19,f20,f22,f192,f23,f272]
def e1321 : List ℕ := [f19,f20,f21,f22,f192,f23,f272]
def e1322 : List ℕ := [f19,f20,f193,f22,f23,f272]
def e1323 : List ℕ := [f19,f20,f193,f21,f22,f23,f272]
def e1324 : List ℕ := [f19,f20,f21,f105,f22,f23,f272]
def e1325 : List ℕ := [f106,f19,f20,f21,f22,f23,f272]
def e1326 : List ℕ := [f19,f20,f21,f22,f23,f162,f272]
def e1327 : List ℕ := [f19,f20,f163,f21,f22,f23,f272]
def e1328 : List ℕ := [f19,f20,f21,f22,f109,f23,f272]
def e1329 : List ℕ := [f110,f19,f20,f21,f22,f23,f272]
def e1330 : List ℕ := [f19,f20,f21,f22,f23,f272,f387]
def e1331 : List ℕ := [f19,f20,f165,f21,f22,f23,f272]
def e1332 : List ℕ := [f19,f20,f21,f22,f23,f316,f272]
def e1333 : List ℕ := [f19,f20,f21,f126,f22,f23,f272]
def e1334 : List ℕ := [f19,f20,f21,f23,f130,f272]
def e1335 : List ℕ := [f19,f20,f21,f22,f130,f272]
def e1336 : List ℕ := [f19,f20,f21,f22,f23,f130,f272]
def e1337 : List ℕ := [f19,f131,f20,f21,f23,f272]
def e1338 : List ℕ := [f19,f131,f20,f21,f22,f23,f272]
def e1339 : List ℕ := [f19,f20,f21,f132,f22,f272]
def e1340 : List ℕ := [f19,f20,f21,f132,f22,f23,f272]
def e1341 : List ℕ := [f133,f19,f20,f21,f22,f23,f272]
def e1342 : List ℕ := [f19,f20,f21,f22,f23,f388]
def e1343 : List ℕ := [f19,f20,f21,f22,f23,f272,f388]
def e1344 : List ℕ := [f19,f20,f21,f135,f22,f23,f272]
def e1345 : List ℕ := [f19,f20,f21,f22,f23,f389]
def e1346 : List ℕ := [f19,f20,f21,f22,f23,f389,f272]
def e1347 : List ℕ := [f137,f19,f20,f21,f22,f23,f272]
def e1348 : List ℕ := [f19,f20,f21,f22,f23,f272,f390]
def e1349 : List ℕ := [f19,f20,f21,f22,f139,f23,f272]
def e1350 : List ℕ := [f19,f20,f21,f22,f23,f324,f272]
def e1351 : List ℕ := [f20,f76,f21,f22,f23,f272,f24]
def e1352 : List ℕ := [f19,f76,f21,f22,f23,f272,f24]
def e1353 : List ℕ := [f19,f280,f21,f22,f23,f272,f24]
def e1354 : List ℕ := [f20,f21,f22,f292,f23,f272,f24]
def e1355 : List ℕ := [f19,f20,f21,f292,f23,f272,f24]
def e1356 : List ℕ := [f293,f20,f21,f22,f23,f272,f24]
def e1357 : List ℕ := [f19,f20,f21,f294,f23,f272,f24]
def e1358 : List ℕ := [f19,f20,f21,f22,f298,f272,f24]
def e1359 : List ℕ := [f19,f20,f21,f22,f269,f272,f24]
def e1360 : List ℕ := [f270,f19,f20,f21,f22,f23,f272]
def e1361 : List ℕ := [f358,f20,f21,f22,f23,f272,f24]
def e1362 : List ℕ := [f358,f19,f20,f21,f22,f23,f272]
def e1363 : List ℕ := [f33,f34,f379,f83]
def e1364 : List ℕ := [f19,f21,f78,f22,f23,f272,f24]
def e1365 : List ℕ := [f19,f20,f78,f22,f23,f272,f24]
def e1366 : List ℕ := [f19,f79,f21,f22,f23,f272,f24]
def e1367 : List ℕ := [f19,f98,f20,f22,f23,f272,f24]
def e1368 : List ℕ := [f19,f21,f22,f155,f23,f272,f24]
def e1369 : List ℕ := [f19,f20,f21,f155,f23,f272,f24]
def e1370 : List ℕ := [f19,f174,f21,f22,f23,f272,f24]
def e1371 : List ℕ := [f19,f20,f21,f175,f23,f272,f24]
def e1372 : List ℕ := [f19,f20,f21,f22,f177,f272,f24]
def e1373 : List ℕ := [f19,f20,f21,f22,f179,f272,f24]
def e1374 : List ℕ := [f180,f19,f20,f21,f22,f23,f24]
def e1375 : List ℕ := [f19,f20,f21,f22,f23,f24,f386]
def e1376 : List ℕ := [f19,f203,f20,f21,f22,f23,f24]
def e1377 : List ℕ := [f19,f20,f21,f22,f23,f125,f24]
def e1378 : List ℕ := [f19,f20,f21,f22,f23,f272,f189]
def e1379 : List ℕ := [f19,f20,f21,f22,f23,f204,f272]
def e1380 : List ℕ := [f19,f20,f22,f192,f23,f272,f24]
def e1381 : List ℕ := [f19,f20,f193,f22,f23,f272,f24]
def e1382 : List ℕ := [f110,f19,f20,f21,f22,f23,f24]
def e1383 : List ℕ := [f13,f4,f11,f7,f391]
def e1384 : List ℕ := [f19,f20,f21,f22,f23,f24,f387]
def e1385 : List ℕ := [f19,f20,f165,f21,f22,f23,f24]
def e1386 : List ℕ := [f13,f4,f11,f17,f7]
def e1387 : List ℕ := [f19,f20,f21,f22,f23,f272,f164]
def e1388 : List ℕ := [f19,f20,f21,f22,f23,f113,f272]
def e1389 : List ℕ := [f19,f20,f21,f23,f130,f272,f24]
def e1390 : List ℕ := [f19,f20,f21,f22,f130,f272,f24]
def e1391 : List ℕ := [f19,f131,f20,f21,f23,f272,f24]
def e1392 : List ℕ := [f19,f20,f21,f132,f22,f272,f24]
def e1393 : List ℕ := [f133,f19,f20,f21,f22,f23,f24]
def e1394 : List ℕ := [f19,f20,f21,f22,f23,f24,f388]
def e1395 : List ℕ := [f19,f20,f21,f135,f22,f23,f24]
def e1396 : List ℕ := [f19,f20,f21,f22,f23,f389,f24]
def e1397 : List ℕ := [f19,f20,f21,f22,f23,f272,f134]
def e1398 : List ℕ := [f19,f20,f21,f22,f23,f136,f272]
def e1399 : List ℕ := [f137,f19,f20,f21,f22,f23,f24]
def e1400 : List ℕ := [f19,f20,f21,f22,f23,f24,f390]
def e1401 : List ℕ := [f19,f20,f21,f22,f139,f23,f24]
def e1402 : List ℕ := [f19,f20,f21,f22,f23,f324,f24]
def e1403 : List ℕ := [f19,f20,f21,f22,f23,f272,f138]
def e1404 : List ℕ := [f19,f20,f21,f22,f23,f140,f272]
def e1405 : List ℕ := [f19,f77,f20,f21,f22,f23,f24]
def e1411 : List ℕ := [f252,f250,f251,f256,f365]
def e1426 : List ℕ := [f40,f52,f63,f61,f44]
def e1427 : List ℕ := [f19,f21,f78,f22,f23,f24]
def e1447 : List ℕ := [f18,f19,f20,f78,f22,f23,f24]
def e1448 : List ℕ := [f19,f20,f76,f78,f22,f23,f24]
def e1449 : List ℕ := [f75,f19,f20,f78,f22,f23,f24]
def e1450 : List ℕ := [f19,f280,f20,f78,f22,f23,f24]
def e1451 : List ℕ := [f408,f19,f20,f78,f22,f23,f24]
def e1452 : List ℕ := [f19,f20,f78,f99,f22,f23,f24]
def e1453 : List ℕ := [f261,f19,f20,f78,f22,f23,f24]
def e1454 : List ℕ := [f19,f20,f409,f22,f23,f24]
def e1455 : List ℕ := [f19,f20,f409,f78,f22,f23,f24]
def e1456 : List ℕ := [f291,f19,f20,f78,f22,f23,f24]
def e1457 : List ℕ := [f20,f78,f22,f292,f23,f24]
def e1458 : List ℕ := [f19,f20,f78,f292,f23,f24]
def e1459 : List ℕ := [f19,f20,f78,f22,f292,f23,f24]
def e1460 : List ℕ := [f293,f20,f78,f22,f23,f24]
def e1461 : List ℕ := [f293,f19,f20,f78,f22,f23,f24]
def e1462 : List ℕ := [f19,f20,f78,f294,f23,f24]
def e1463 : List ℕ := [f19,f20,f78,f294,f22,f23,f24]
def e1464 : List ℕ := [f266,f19,f20,f78,f22,f23,f24]
def e1465 : List ℕ := [f19,f20,f78,f22,f298,f24]
def e1466 : List ℕ := [f19,f20,f78,f22,f23,f298,f24]
def e1467 : List ℕ := [f325,f19,f20,f78,f22,f23,f24]
def e1468 : List ℕ := [f19,f20,f78,f22,f269,f24]
def e1469 : List ℕ := [f19,f20,f78,f22,f269,f23,f24]
def e1470 : List ℕ := [f270,f19,f20,f78,f22,f23,f24]
def e1471 : List ℕ := [f358,f19,f20,f78,f22,f23,f24]
def e1472 : List ℕ := [f19,f98,f78,f22,f23,f24]
def e1473 : List ℕ := [f19,f98,f20,f22,f23,f24]
def e1474 : List ℕ := [f19,f98,f20,f78,f22,f23,f24]
def e1475 : List ℕ := [f19,f141,f20,f78,f22,f23,f24]
def e1476 : List ℕ := [f19,f20,f78,f155,f23,f24]
def e1477 : List ℕ := [f19,f20,f78,f22,f155,f23,f24]
def e1478 : List ℕ := [f19,f174,f20,f78,f22,f23,f24]
def e1479 : List ℕ := [f19,f20,f78,f175,f23,f24]
def e1480 : List ℕ := [f19,f20,f78,f175,f22,f23,f24]
def e1481 : List ℕ := [f176,f19,f20,f78,f22,f23,f24]
def e1482 : List ℕ := [f19,f78,f22,f23,f177,f24]
def e1483 : List ℕ := [f19,f20,f78,f22,f23,f177,f24]
def e1484 : List ℕ := [f19,f178,f78,f22,f23,f24]
def e1485 : List ℕ := [f19,f178,f20,f78,f22,f23,f24]
def e1486 : List ℕ := [f19,f20,f78,f22,f179,f23,f24]
def e1487 : List ℕ := [f180,f19,f20,f78,f22,f23,f24]
def e1488 : List ℕ := [f252,f250,f251,f365,f410]
def e1489 : List ℕ := [f19,f78,f22,f23,f24,f189]
def e1490 : List ℕ := [f19,f20,f78,f22,f23,f24,f189]
def e1491 : List ℕ := [f19,f203,f78,f22,f23,f24]
def e1492 : List ℕ := [f19,f203,f20,f78,f22,f23,f24]
def e1493 : List ℕ := [f19,f20,f78,f22,f23,f204,f24]
def e1494 : List ℕ := [f19,f411,f20,f78,f22,f23,f24]
def e1495 : List ℕ := [f19,f20,f22,f160,f23,f24]
def e1496 : List ℕ := [f19,f20,f78,f22,f160,f23,f24]
def e1497 : List ℕ := [f19,f20,f412,f22,f23,f24]
def e1498 : List ℕ := [f19,f20,f412,f78,f22,f23,f24]
def e1499 : List ℕ := [f19,f20,f78,f413,f22,f23,f24]
def e1500 : List ℕ := [f414,f19,f20,f78,f22,f23,f24]
def e1501 : List ℕ := [f19,f20,f78,f22,f23,f415,f24]
def e1502 : List ℕ := [f19,f20,f416,f78,f22,f23,f24]
def e1503 : List ℕ := [f19,f20,f78,f22,f417,f23,f24]
def e1504 : List ℕ := [f418,f19,f20,f78,f22,f23,f24]
def e1507 : List ℕ := [f40,f41,f42,f43,f44]
def e1508 : List ℕ := [f40,f41,f42,f43,f44,f421]
def e1509 : List ℕ := [f19,f20,f78,f22,f23,f24,f422]
def e1510 : List ℕ := [f19,f20,f423,f78,f22,f23,f24]
def e1511 : List ℕ := [f19,f20,f78,f22,f23,f424,f24]
def e1512 : List ℕ := [f19,f20,f78,f126,f22,f23,f24]
def e1513 : List ℕ := [f19,f20,f78,f23,f130,f24]
def e1514 : List ℕ := [f19,f20,f78,f22,f130,f24]
def e1515 : List ℕ := [f19,f20,f78,f22,f23,f130,f24]
def e1516 : List ℕ := [f19,f131,f20,f78,f23,f24]
def e1517 : List ℕ := [f19,f131,f20,f78,f22,f23,f24]
def e1518 : List ℕ := [f19,f20,f78,f132,f22,f24]
def e1519 : List ℕ := [f19,f20,f78,f132,f22,f23,f24]
def e1520 : List ℕ := [f133,f19,f20,f78,f22,f23,f24]
def e1521 : List ℕ := [f19,f20,f78,f22,f23,f134]
def e1522 : List ℕ := [f19,f20,f78,f22,f23,f24,f134]
def e1523 : List ℕ := [f19,f20,f78,f135,f22,f23,f24]
def e1524 : List ℕ := [f19,f20,f78,f22,f23,f136]
def e1525 : List ℕ := [f19,f20,f78,f22,f23,f136,f24]
def e1526 : List ℕ := [f137,f19,f20,f78,f22,f23,f24]
def e1527 : List ℕ := [f19,f20,f78,f22,f23,f24,f138]
def e1528 : List ℕ := [f19,f20,f78,f22,f139,f23,f24]
def e1529 : List ℕ := [f19,f20,f78,f22,f23,f140,f24]
def e1530 : List ℕ := [f19,f20,f78,f22,f23,f24]
def e1531 : List ℕ := [f18,f19,f21,f78,f22,f23,f24]
def e1532 : List ℕ := [f19,f76,f21,f78,f22,f23,f24]
def e1533 : List ℕ := [f75,f19,f21,f78,f22,f23,f24]
def e1534 : List ℕ := [f19,f280,f21,f78,f22,f23,f24]
def e1535 : List ℕ := [f97,f19,f20,f78,f22,f23,f24]
def e1536 : List ℕ := [f361,f19,f20,f78,f22,f23,f24]
def e1537 : List ℕ := [f19,f20,f262,f78,f22,f23,f24]
def e1538 : List ℕ := [f408,f19,f20,f21,f22,f23,f24]
def e1539 : List ℕ := [f261,f19,f20,f21,f22,f23,f24]
def e1540 : List ℕ := [f19,f20,f21,f409,f22,f23,f24]
def e1541 : List ℕ := [f20,f21,f78,f22,f292,f23,f24]
def e1542 : List ℕ := [f19,f20,f21,f78,f292,f23,f24]
def e1543 : List ℕ := [f293,f20,f21,f78,f22,f23,f24]
def e1544 : List ℕ := [f19,f20,f21,f78,f294,f23,f24]
def e1545 : List ℕ := [f19,f20,f21,f78,f22,f298,f24]
def e1546 : List ℕ := [f19,f20,f21,f78,f22,f269,f24]
def e1547 : List ℕ := [f19,f77,f21,f78,f22,f23,f24]
def e1548 : List ℕ := [f19,f77,f20,f78,f22,f23,f24]
def e1549 : List ℕ := [f19,f79,f78,f22,f23,f24]
def e1550 : List ℕ := [f19,f79,f21,f78,f22,f23,f24]
def e1551 : List ℕ := [f19,f79,f20,f78,f22,f23,f24]
def e1552 : List ℕ := [f19,f98,f21,f78,f22,f23,f24]
def e1553 : List ℕ := [f19,f98,f20,f21,f22,f23,f24]
def e1554 : List ℕ := [f19,f141,f21,f78,f22,f23,f24]
def e1555 : List ℕ := [f19,f21,f78,f22,f155,f23,f24]
def e1556 : List ℕ := [f19,f20,f21,f78,f155,f23,f24]
def e1557 : List ℕ := [f19,f174,f21,f78,f22,f23,f24]
def e1558 : List ℕ := [f19,f21,f78,f175,f23,f24]
def e1559 : List ℕ := [f19,f21,f78,f175,f22,f23,f24]
def e1560 : List ℕ := [f19,f20,f21,f78,f175,f23,f24]
def e1561 : List ℕ := [f176,f19,f21,f78,f22,f23,f24]
def e1562 : List ℕ := [f19,f21,f78,f22,f23,f177,f24]
def e1563 : List ℕ := [f19,f20,f21,f78,f22,f177,f24]
def e1564 : List ℕ := [f19,f178,f21,f78,f22,f23,f24]
def e1565 : List ℕ := [f2,f425,f211,f426]
def e1566 : List ℕ := [f19,f21,f78,f22,f179,f24]
def e1567 : List ℕ := [f19,f21,f78,f22,f179,f23,f24]
def e1568 : List ℕ := [f19,f20,f21,f78,f22,f179,f24]
def e1569 : List ℕ := [f180,f19,f21,f78,f22,f23,f24]
def e1570 : List ℕ := [f19,f21,f78,f22,f23,f24,f189]
def e1571 : List ℕ := [f19,f20,f21,f78,f22,f23,f189]
def e1572 : List ℕ := [f19,f203,f21,f78,f22,f23,f24]
def e1573 : List ℕ := [f33,f34,f379,f37]
def e1574 : List ℕ := [f19,f21,f78,f22,f23,f204]
def e1575 : List ℕ := [f19,f21,f78,f22,f23,f204,f24]
def e1576 : List ℕ := [f19,f20,f21,f78,f22,f23,f204]
def e1577 : List ℕ := [f19,f79,f20,f21,f22,f23,f24]
def e1578 : List ℕ := [f102,f19,f20,f78,f22,f23,f24]
def e1579 : List ℕ := [f19,f20,f78,f22,f192,f23,f24]
def e1580 : List ℕ := [f19,f20,f193,f78,f22,f23,f24]
def e1581 : List ℕ := [f19,f20,f78,f105,f22,f23,f24]
def e1582 : List ℕ := [f106,f19,f20,f78,f22,f23,f24]
def e1583 : List ℕ := [f19,f20,f78,f22,f23,f162,f24]
def e1584 : List ℕ := [f19,f20,f163,f78,f22,f23,f24]
def e1585 : List ℕ := [f19,f20,f78,f22,f109,f23,f24]
def e1586 : List ℕ := [f110,f19,f20,f78,f22,f23,f24]
def e1594 : List ℕ := [f19,f20,f78,f22,f23,f24,f164]
def e1595 : List ℕ := [f19,f20,f165,f78,f22,f23,f24]
def e1596 : List ℕ := [f19,f20,f78,f22,f23,f113,f24]
def e1597 : List ℕ := [f19,f411,f20,f21,f22,f23,f24]
def e1598 : List ℕ := [f19,f20,f21,f22,f160,f23,f24]
def e1599 : List ℕ := [f19,f20,f21,f412,f22,f23,f24]
def e1600 : List ℕ := [f19,f20,f21,f413,f22,f23,f24]
def e1601 : List ℕ := [f414,f19,f20,f21,f22,f23,f24]
def e1602 : List ℕ := [f19,f20,f21,f22,f23,f415,f24]
def e1603 : List ℕ := [f19,f20,f21,f416,f22,f23,f24]
def e1604 : List ℕ := [f19,f20,f21,f22,f417,f23,f24]
def e1605 : List ℕ := [f418,f19,f20,f21,f22,f23,f24]
def e1606 : List ℕ := [f19,f20,f21,f22,f23,f24,f422]
def e1607 : List ℕ := [f19,f20,f21,f423,f22,f23,f24]
def e1608 : List ℕ := [f19,f20,f21,f22,f23,f424,f24]
def e1609 : List ℕ := [f19,f20,f21,f78,f23,f130,f24]
def e1610 : List ℕ := [f19,f20,f21,f78,f22,f130,f24]
def e1611 : List ℕ := [f19,f131,f20,f21,f78,f23,f24]
def e1612 : List ℕ := [f19,f20,f21,f78,f132,f22,f24]
def e1613 : List ℕ := [f19,f20,f21,f78,f22,f23,f134]
def e1614 : List ℕ := [f19,f20,f21,f78,f22,f23,f136]
def e1615 : List ℕ := [f19,f20,f21,f78,f22,f23,f24]
def e1635 : List ℕ := [f40,f438,f52,f61,f44]
def e1636 : List ℕ := [f19,f79,f21,f22,f23,f24]
def e1666 : List ℕ := [f97,f19,f98,f20,f22,f23,f24]
def e1667 : List ℕ := [f19,f445,f20,f22,f23,f24]
def e1668 : List ℕ := [f19,f98,f445,f20,f22,f23,f24]
def e1669 : List ℕ := [f361,f19,f98,f20,f22,f23,f24]
def e1670 : List ℕ := [f19,f100,f98,f20,f22,f23,f24]
def e1671 : List ℕ := [f18,f19,f98,f20,f22,f23,f24]
def e1672 : List ℕ := [f19,f98,f76,f22,f23,f24]
def e1673 : List ℕ := [f19,f98,f20,f76,f22,f23,f24]
def e1674 : List ℕ := [f75,f19,f98,f20,f22,f23,f24]
def e1675 : List ℕ := [f19,f98,f280,f22,f23,f24]
def e1676 : List ℕ := [f19,f98,f280,f20,f22,f23,f24]
def e1677 : List ℕ := [f291,f19,f98,f20,f22,f23,f24]
def e1678 : List ℕ := [f98,f20,f22,f292,f23,f24]
def e1679 : List ℕ := [f19,f98,f20,f292,f23,f24]
def e1680 : List ℕ := [f19,f98,f20,f22,f292,f23,f24]
def e1681 : List ℕ := [f293,f98,f20,f22,f23,f24]
def e1682 : List ℕ := [f293,f19,f98,f20,f22,f23,f24]
def e1683 : List ℕ := [f19,f98,f20,f294,f23,f24]
def e1684 : List ℕ := [f19,f98,f20,f294,f22,f23,f24]
def e1685 : List ℕ := [f266,f19,f98,f20,f22,f23,f24]
def e1686 : List ℕ := [f19,f98,f20,f22,f298,f24]
def e1687 : List ℕ := [f19,f98,f20,f22,f23,f298,f24]
def e1688 : List ℕ := [f325,f19,f98,f20,f22,f23,f24]
def e1689 : List ℕ := [f19,f98,f20,f22,f269,f24]
def e1690 : List ℕ := [f19,f98,f20,f22,f269,f23,f24]
def e1691 : List ℕ := [f270,f19,f98,f20,f22,f23,f24]
def e1692 : List ℕ := [f358,f19,f98,f20,f22,f23,f24]
def e1693 : List ℕ := [f102,f19,f98,f20,f22,f23,f24]
def e1694 : List ℕ := [f19,f20,f22,f103,f23,f24]
def e1695 : List ℕ := [f19,f98,f20,f22,f103,f23,f24]
def e1696 : List ℕ := [f19,f104,f20,f22,f23,f24]
def e1697 : List ℕ := [f19,f104,f98,f20,f22,f23,f24]
def e1698 : List ℕ := [f19,f98,f20,f105,f22,f23,f24]
def e1699 : List ℕ := [f106,f19,f98,f20,f22,f23,f24]
def e1700 : List ℕ := [f19,f98,f20,f22,f23,f107,f24]
def e1701 : List ℕ := [f19,f108,f98,f20,f22,f23,f24]
def e1702 : List ℕ := [f19,f98,f20,f22,f109,f23,f24]
def e1703 : List ℕ := [f110,f19,f98,f20,f22,f23,f24]
def e1704 : List ℕ := [f19,f98,f20,f22,f23,f24,f111]
def e1705 : List ℕ := [f19,f112,f98,f20,f22,f23,f24]
def e1706 : List ℕ := [f19,f98,f20,f22,f23,f113,f24]
def e1707 : List ℕ := [f19,f141,f98,f20,f22,f23,f24]
def e1708 : List ℕ := [f19,f98,f22,f155,f23,f24]
def e1709 : List ℕ := [f19,f98,f20,f155,f23,f24]
def e1710 : List ℕ := [f19,f98,f20,f22,f155,f23,f24]
def e1711 : List ℕ := [f19,f98,f174,f22,f23,f24]
def e1712 : List ℕ := [f19,f98,f174,f20,f22,f23,f24]
def e1713 : List ℕ := [f19,f98,f20,f175,f23,f24]
def e1714 : List ℕ := [f19,f98,f20,f175,f22,f23,f24]
def e1715 : List ℕ := [f176,f19,f98,f20,f22,f23,f24]
def e1716 : List ℕ := [f19,f98,f20,f22,f23,f177,f24]
def e1717 : List ℕ := [f19,f98,f178,f20,f22,f23,f24]
def e1718 : List ℕ := [f19,f98,f20,f22,f179,f23,f24]
def e1719 : List ℕ := [f180,f19,f98,f20,f22,f23,f24]
def e1720 : List ℕ := [f19,f98,f20,f22,f23,f24,f189]
def e1721 : List ℕ := [f19,f98,f203,f20,f22,f23,f24]
def e1722 : List ℕ := [f19,f98,f20,f22,f23,f204,f24]
def e1723 : List ℕ := [f19,f98,f20,f126,f22,f23,f24]
def e1724 : List ℕ := [f19,f98,f20,f23,f130,f24]
def e1725 : List ℕ := [f19,f98,f20,f22,f130,f24]
def e1726 : List ℕ := [f19,f98,f20,f22,f23,f130,f24]
def e1727 : List ℕ := [f19,f131,f98,f20,f23,f24]
def e1728 : List ℕ := [f19,f131,f98,f20,f22,f23,f24]
def e1729 : List ℕ := [f19,f98,f20,f132,f22,f24]
def e1730 : List ℕ := [f19,f98,f20,f132,f22,f23,f24]
def e1731 : List ℕ := [f133,f19,f98,f20,f22,f23,f24]
def e1732 : List ℕ := [f19,f98,f20,f22,f23,f134]
def e1733 : List ℕ := [f19,f98,f20,f22,f23,f24,f134]
def e1734 : List ℕ := [f19,f98,f20,f135,f22,f23,f24]
def e1735 : List ℕ := [f19,f98,f20,f22,f23,f136]
def e1736 : List ℕ := [f19,f98,f20,f22,f23,f136,f24]
def e1737 : List ℕ := [f137,f19,f98,f20,f22,f23,f24]
def e1738 : List ℕ := [f19,f98,f20,f22,f23,f24,f138]
def e1739 : List ℕ := [f19,f98,f20,f22,f139,f23,f24]
def e1740 : List ℕ := [f19,f98,f20,f22,f23,f140,f24]
def e1741 : List ℕ := [f19,f141,f20,f21,f22,f23,f24]
def e1776 : List ℕ := [f97,f19,f21,f22,f155,f23,f24]
def e1777 : List ℕ := [f361,f19,f21,f22,f155,f23,f24]
def e1778 : List ℕ := [f19,f262,f21,f22,f155,f23,f24]
def e1779 : List ℕ := [f291,f19,f21,f22,f155,f23,f24]
def e1780 : List ℕ := [f21,f292,f155,f23,f24]
def e1781 : List ℕ := [f21,f22,f292,f155,f23,f24]
def e1782 : List ℕ := [f19,f21,f292,f155,f23,f24]
def e1783 : List ℕ := [f19,f21,f22,f292,f155,f23,f24]
def e1784 : List ℕ := [f293,f21,f22,f155,f23,f24]
def e1785 : List ℕ := [f293,f19,f21,f22,f155,f23,f24]
def e1786 : List ℕ := [f19,f21,f294,f155,f23,f24]
def e1787 : List ℕ := [f19,f21,f294,f22,f155,f23,f24]
def e1788 : List ℕ := [f452,f19,f21,f22,f155,f23,f24]
def e1789 : List ℕ := [f21,f22,f155,f115,f23,f24]
def e1790 : List ℕ := [f19,f21,f22,f115,f23,f24]
def e1791 : List ℕ := [f19,f21,f22,f155,f115,f23,f24]
def e1792 : List ℕ := [f158,f21,f22,f155,f23,f24]
def e1793 : List ℕ := [f158,f19,f21,f22,f155,f23,f24]
def e1794 : List ℕ := [f19,f21,f22,f453,f23,f24]
def e1795 : List ℕ := [f19,f21,f22,f453,f155,f23,f24]
def e1796 : List ℕ := [f266,f19,f21,f22,f155,f23,f24]
def e1797 : List ℕ := [f19,f21,f22,f155,f298,f24]
def e1798 : List ℕ := [f19,f21,f22,f155,f23,f298,f24]
def e1799 : List ℕ := [f325,f19,f21,f22,f155,f23,f24]
def e1800 : List ℕ := [f19,f21,f22,f155,f269,f24]
def e1801 : List ℕ := [f19,f21,f22,f155,f269,f23,f24]
def e1802 : List ℕ := [f270,f19,f21,f22,f155,f23,f24]
def e1803 : List ℕ := [f358,f19,f21,f22,f155,f23,f24]
def e1804 : List ℕ := [f102,f19,f21,f22,f155,f23,f24]
def e1805 : List ℕ := [f19,f21,f22,f155,f192,f23,f24]
def e1806 : List ℕ := [f19,f193,f21,f22,f155,f23,f24]
def e1807 : List ℕ := [f19,f21,f105,f22,f155,f23,f24]
def e1808 : List ℕ := [f19,f159,f21,f22,f155,f23,f24]
def e1809 : List ℕ := [f19,f21,f22,f160,f23,f24]
def e1810 : List ℕ := [f19,f21,f22,f155,f160,f23,f24]
def e1811 : List ℕ := [f19,f104,f21,f22,f155,f23,f24]
def e1812 : List ℕ := [f19,f21,f22,f161,f23,f24]
def e1813 : List ℕ := [f19,f21,f22,f161,f155,f23,f24]
def e1814 : List ℕ := [f33,f34,f143,f83]
def e1815 : List ℕ := [f106,f19,f21,f22,f155,f23,f24]
def e1816 : List ℕ := [f19,f21,f22,f155,f23,f162,f24]
def e1817 : List ℕ := [f19,f163,f21,f22,f155,f23,f24]
def e1818 : List ℕ := [f19,f21,f22,f155,f109,f23,f24]
def e1819 : List ℕ := [f110,f19,f21,f22,f155,f23,f24]
def e1820 : List ℕ := [f19,f21,f22,f155,f23,f24,f164]
def e1821 : List ℕ := [f19,f165,f21,f22,f155,f23,f24]
def e1822 : List ℕ := [f19,f21,f22,f155,f23,f113,f24]
def e1823 : List ℕ := [f19,f174,f21,f155,f23,f24]
def e1824 : List ℕ := [f19,f174,f21,f22,f23,f24]
def e1825 : List ℕ := [f19,f174,f21,f22,f155,f23,f24]
def e1826 : List ℕ := [f19,f21,f126,f22,f155,f23,f24]
def e1827 : List ℕ := [f19,f21,f22,f155,f130,f24]
def e1828 : List ℕ := [f19,f21,f22,f155,f23,f130,f24]
def e1829 : List ℕ := [f19,f131,f21,f22,f155,f23,f24]
def e1830 : List ℕ := [f19,f21,f132,f22,f155,f24]
def e1831 : List ℕ := [f19,f21,f132,f22,f155,f23,f24]
def e1832 : List ℕ := [f133,f19,f21,f22,f155,f23,f24]
def e1833 : List ℕ := [f248,f250,f446,f365,f454]
def e1834 : List ℕ := [f19,f21,f155,f23,f24,f134]
def e1835 : List ℕ := [f19,f21,f22,f155,f23,f24,f134]
def e1836 : List ℕ := [f19,f21,f135,f155,f23,f24]
def e1837 : List ℕ := [f19,f21,f135,f22,f155,f23,f24]
def e1838 : List ℕ := [f19,f21,f22,f155,f23,f136,f24]
def e1839 : List ℕ := [f19,f21,f166,f22,f155,f23,f24]
def e1840 : List ℕ := [f19,f21,f22,f155,f167,f24]
def e1841 : List ℕ := [f19,f21,f22,f155,f23,f167,f24]
def e1842 : List ℕ := [f19,f168,f21,f22,f155,f23,f24]
def e1843 : List ℕ := [f19,f21,f169,f22,f155,f24]
def e1844 : List ℕ := [f19,f21,f169,f22,f155,f23,f24]
def e1845 : List ℕ := [f170,f19,f21,f22,f155,f23,f24]
def e1846 : List ℕ := [f19,f21,f22,f155,f23,f24,f171]
def e1847 : List ℕ := [f19,f21,f22,f172,f155,f23,f24]
def e1848 : List ℕ := [f19,f21,f22,f155,f23,f173,f24]
def e1849 : List ℕ := [f137,f19,f21,f22,f155,f23,f24]
def e1877 : List ℕ := [f248,f250,f251,f446,f365]
def e1878 : List ℕ := [f248,f250,f251,f446,f460]
def e1879 : List ℕ := [f248,f250,f251,f446,f365,f460]
def e1880 : List ℕ := [f19,f21,f22,f155,f23,f24,f138]
def e1881 : List ℕ := [f19,f21,f22,f155,f139,f23,f24]
def e1882 : List ℕ := [f1,f2,f461,f3]
def e1883 : List ℕ := [f19,f21,f22,f155,f23,f140,f24]
def e1884 : List ℕ := [f19,f21,f22,f155,f23,f24]
def e1885 : List ℕ := [f19,f20,f21,f155,f23,f24]
def e1886 : List ℕ := [f19,f20,f21,f22,f155,f23,f24]
def e1911 : List ℕ := [f468,f19,f174,f21,f22,f23,f24]
def e1912 : List ℕ := [f174,f469,f21,f22,f23,f24]
def e1913 : List ℕ := [f19,f469,f21,f22,f23,f24]
def e1914 : List ℕ := [f19,f174,f469,f21,f22,f23,f24]
def e1915 : List ℕ := [f470,f174,f21,f22,f23,f24]
def e1916 : List ℕ := [f470,f19,f174,f21,f22,f23,f24]
def e1917 : List ℕ := [f19,f471,f21,f22,f23,f24]
def e1918 : List ℕ := [f19,f471,f174,f21,f22,f23,f24]
def e1919 : List ℕ := [f97,f19,f174,f21,f22,f23,f24]
def e1920 : List ℕ := [f361,f19,f174,f21,f22,f23,f24]
def e1921 : List ℕ := [f19,f174,f262,f21,f22,f23,f24]
def e1922 : List ℕ := [f291,f19,f174,f21,f22,f23,f24]
def e1923 : List ℕ := [f174,f21,f22,f292,f23,f24]
def e1924 : List ℕ := [f19,f174,f21,f292,f23,f24]
def e1925 : List ℕ := [f19,f174,f21,f22,f292,f23,f24]
def e1926 : List ℕ := [f293,f174,f21,f22,f23,f24]
def e1927 : List ℕ := [f293,f19,f174,f21,f22,f23,f24]
def e1928 : List ℕ := [f19,f174,f21,f294,f23,f24]
def e1929 : List ℕ := [f19,f174,f21,f294,f22,f23,f24]
def e1930 : List ℕ := [f266,f19,f174,f21,f22,f23,f24]
def e1931 : List ℕ := [f19,f174,f21,f22,f298,f24]
def e1932 : List ℕ := [f19,f174,f21,f22,f23,f298,f24]
def e1933 : List ℕ := [f325,f19,f174,f21,f22,f23,f24]
def e1934 : List ℕ := [f19,f174,f21,f22,f269,f24]
def e1935 : List ℕ := [f19,f174,f21,f22,f269,f23,f24]
def e1936 : List ℕ := [f270,f19,f174,f21,f22,f23,f24]
def e1937 : List ℕ := [f358,f19,f174,f21,f22,f23,f24]
def e1938 : List ℕ := [f19,f77,f174,f21,f22,f23,f24]
def e1939 : List ℕ := [f19,f21,f472,f22,f23,f24]
def e1940 : List ℕ := [f19,f174,f472,f22,f23,f24]
def e1941 : List ℕ := [f19,f174,f21,f472,f22,f23,f24]
def e1942 : List ℕ := [f473,f19,f21,f22,f23,f24]
def e1943 : List ℕ := [f473,f19,f174,f21,f22,f23,f24]
def e1944 : List ℕ := [f19,f98,f174,f21,f22,f23,f24]
def e1945 : List ℕ := [f176,f19,f174,f21,f22,f23,f24]
def e1946 : List ℕ := [f19,f174,f21,f22,f474,f24]
def e1947 : List ℕ := [f19,f174,f21,f22,f23,f474,f24]
def e1948 : List ℕ := [f19,f475,f174,f21,f22,f23,f24]
def e1949 : List ℕ := [f19,f174,f21,f22,f179,f24]
def e1950 : List ℕ := [f19,f174,f21,f22,f179,f23,f24]
def e1951 : List ℕ := [f180,f19,f174,f21,f22,f23,f24]
def e1952 : List ℕ := [f19,f174,f21,f22,f23,f476]
def e1953 : List ℕ := [f19,f174,f21,f22,f23,f24,f476]
def e1954 : List ℕ := [f19,f477,f174,f21,f22,f23,f24]
def e1955 : List ℕ := [f19,f174,f21,f22,f23,f204]
def e1956 : List ℕ := [f19,f174,f21,f22,f23,f204,f24]
def e1957 : List ℕ := [f102,f19,f174,f21,f22,f23,f24]
def e1958 : List ℕ := [f19,f174,f21,f22,f192,f23,f24]
def e1959 : List ℕ := [f19,f174,f193,f21,f22,f23,f24]
def e1960 : List ℕ := [f19,f174,f21,f105,f22,f23,f24]
def e1961 : List ℕ := [f33,f478,f34,f83]
def e1962 : List ℕ := [f106,f19,f174,f21,f22,f23,f24]
def e1963 : List ℕ := [f19,f174,f21,f22,f23,f162,f24]
def e1964 : List ℕ := [f19,f174,f163,f21,f22,f23,f24]
def e1965 : List ℕ := [f19,f174,f21,f22,f109,f23,f24]
def e1966 : List ℕ := [f110,f19,f174,f21,f22,f23,f24]
def e1967 : List ℕ := [f19,f174,f21,f22,f23,f24,f164]
def e1968 : List ℕ := [f19,f174,f165,f21,f22,f23,f24]
def e1969 : List ℕ := [f19,f174,f21,f22,f23,f113,f24]
def e1970 : List ℕ := [f19,f174,f21,f126,f22,f23,f24]
def e1971 : List ℕ := [f19,f174,f21,f23,f130,f24]
def e1972 : List ℕ := [f19,f174,f21,f22,f130,f24]
def e1973 : List ℕ := [f19,f174,f21,f22,f23,f130,f24]
def e1974 : List ℕ := [f19,f131,f174,f21,f23,f24]
def e1975 : List ℕ := [f19,f131,f174,f21,f22,f23,f24]
def e1976 : List ℕ := [f19,f174,f21,f132,f22,f24]
def e1977 : List ℕ := [f19,f174,f21,f132,f22,f23,f24]
def e1978 : List ℕ := [f133,f19,f174,f21,f22,f23,f24]
def e1979 : List ℕ := [f19,f174,f21,f22,f23,f24,f134]
def e1980 : List ℕ := [f19,f174,f21,f135,f22,f23,f24]
def e1981 : List ℕ := [f19,f174,f21,f22,f23,f136,f24]
def e1982 : List ℕ := [f137,f19,f174,f21,f22,f23,f24]
def e1983 : List ℕ := [f19,f174,f21,f22,f23,f24,f138]
def e1984 : List ℕ := [f19,f174,f21,f22,f139,f23,f24]
def e1985 : List ℕ := [f19,f174,f21,f22,f23,f140,f24]
def e1986 : List ℕ := [f19,f174,f20,f21,f22,f23,f24]
def e1987 : List ℕ := [f19,f20,f21,f175,f23,f24]
def e1988 : List ℕ := [f19,f20,f21,f175,f22,f23,f24]
def e1989 : List ℕ := [f176,f19,f20,f21,f22,f23,f24]
def e1998 : List ℕ := [f18,f19,f20,f21,f22,f177,f24]
def e1999 : List ℕ := [f19,f20,f76,f21,f22,f177,f24]
def e2000 : List ℕ := [f75,f19,f20,f21,f22,f177,f24]
def e2001 : List ℕ := [f19,f280,f20,f21,f22,f177,f24]
def e2002 : List ℕ := [f97,f19,f20,f21,f22,f177,f24]
def e2003 : List ℕ := [f361,f19,f20,f21,f22,f177,f24]
def e2004 : List ℕ := [f19,f20,f262,f21,f22,f177,f24]
def e2005 : List ℕ := [f291,f19,f20,f21,f22,f177,f24]
def e2006 : List ℕ := [f20,f21,f22,f292,f177,f24]
def e2007 : List ℕ := [f19,f20,f21,f292,f177,f24]
def e2008 : List ℕ := [f19,f20,f21,f22,f292,f177,f24]
def e2009 : List ℕ := [f293,f20,f21,f22,f177,f24]
def e2010 : List ℕ := [f293,f19,f20,f21,f22,f177,f24]
def e2011 : List ℕ := [f19,f20,f21,f294,f177,f24]
def e2012 : List ℕ := [f19,f20,f21,f294,f22,f177,f24]
def e2013 : List ℕ := [f483,f19,f20,f21,f22,f177,f24]
def e2014 : List ℕ := [f19,f20,f21,f22,f119,f24]
def e2015 : List ℕ := [f19,f20,f21,f22,f177,f119,f24]
def e2016 : List ℕ := [f268,f19,f20,f21,f22,f177,f24]
def e2017 : List ℕ := [f19,f20,f21,f22,f484,f24]
def e2018 : List ℕ := [f19,f20,f21,f22,f484,f177,f24]
def e2019 : List ℕ := [f270,f19,f20,f21,f22,f177,f24]
def e2020 : List ℕ := [f358,f19,f20,f21,f22,f177,f24]
def e2021 : List ℕ := [f19,f77,f20,f21,f22,f177,f24]
def e2022 : List ℕ := [f19,f79,f20,f21,f22,f177,f24]
def e2023 : List ℕ := [f19,f98,f20,f21,f22,f177,f24]
def e2024 : List ℕ := [f19,f141,f20,f21,f22,f177,f24]
def e2025 : List ℕ := [f19,f21,f22,f155,f177,f24]
def e2026 : List ℕ := [f19,f20,f21,f22,f155,f177,f24]
def e2027 : List ℕ := [f19,f174,f21,f22,f177,f24]
def e2028 : List ℕ := [f19,f174,f20,f21,f22,f177,f24]
def e2029 : List ℕ := [f19,f20,f21,f175,f22,f177,f24]
def e2030 : List ℕ := [f19,f21,f22,f179,f177,f24]
def e2031 : List ℕ := [f19,f20,f21,f22,f179,f24]
def e2032 : List ℕ := [f19,f20,f21,f22,f179,f177,f24]
def e2033 : List ℕ := [f180,f19,f20,f21,f22,f177,f24]
def e2067 : List ℕ := [f97,f19,f21,f22,f177,f189]
def e2068 : List ℕ := [f19,f289,f22,f177,f189]
def e2069 : List ℕ := [f19,f21,f289,f22,f177,f189]
def e2070 : List ℕ := [f361,f19,f21,f22,f177,f189]
def e2071 : List ℕ := [f19,f262,f22,f177,f189]
def e2072 : List ℕ := [f13,f27,f200]
def e2073 : List ℕ := [f19,f262,f21,f22,f177,f189]
def e2074 : List ℕ := [f291,f19,f21,f22,f177,f189]
def e2075 : List ℕ := [f21,f22,f292,f177,f189]
def e2076 : List ℕ := [f19,f21,f292,f177,f189]
def e2077 : List ℕ := [f19,f21,f22,f292,f177,f189]
def e2078 : List ℕ := [f293,f21,f22,f177,f189]
def e2079 : List ℕ := [f293,f19,f21,f22,f177,f189]
def e2080 : List ℕ := [f19,f21,f294,f177,f189]
def e2081 : List ℕ := [f19,f21,f294,f22,f177,f189]
def e2082 : List ℕ := [f483,f19,f21,f22,f177,f189]
def e2083 : List ℕ := [f19,f21,f22,f177,f119,f189]
def e2084 : List ℕ := [f268,f19,f21,f22,f177,f189]
def e2085 : List ℕ := [f19,f21,f22,f484,f177,f189]
def e2086 : List ℕ := [f499,f19,f21,f22,f177,f189]
def e2087 : List ℕ := [f19,f21,f22,f177,f189,f123]
def e2088 : List ℕ := [f191,f19,f21,f22,f177,f189]
def e2089 : List ℕ := [f19,f21,f22,f177,f500,f189]
def e2090 : List ℕ := [f102,f19,f21,f22,f177,f189]
def e2091 : List ℕ := [f19,f22,f192,f177,f189]
def e2092 : List ℕ := [f19,f21,f22,f192,f177,f189]
def e2093 : List ℕ := [f19,f193,f22,f177,f189]
def e2094 : List ℕ := [f19,f193,f21,f22,f177,f189]
def e2095 : List ℕ := [f19,f21,f105,f22,f177,f189]
def e2096 : List ℕ := [f19,f501,f21,f22,f177,f189]
def e2097 : List ℕ := [f19,f21,f22,f177,f415,f189]
def e2098 : List ℕ := [f19,f108,f21,f22,f177,f189]
def e2099 : List ℕ := [f19,f21,f22,f502,f177,f189]
def e2100 : List ℕ := [f19,f196,f21,f22,f177,f189]
def e2101 : List ℕ := [f19,f21,f22,f177,f189,f422]
def e2102 : List ℕ := [f19,f112,f21,f22,f177,f189]
def e2103 : List ℕ := [f19,f21,f22,f177,f503,f189]
def e2104 : List ℕ := [f19,f21,f504,f22,f177,f189]
def e2105 : List ℕ := [f19,f21,f22,f177,f167,f189]
def e2106 : List ℕ := [f505,f19,f21,f22,f177,f189]
def e2107 : List ℕ := [f19,f21,f506,f22,f177,f189]
def e2108 : List ℕ := [f19,f507,f21,f22,f177,f189]
def e2109 : List ℕ := [f19,f21,f22,f177,f171]
def e2110 : List ℕ := [f19,f21,f22,f177,f189,f171]
def e2111 : List ℕ := [f19,f21,f508,f22,f177,f189]
def e2112 : List ℕ := [f19,f21,f22,f177,f198]
def e2113 : List ℕ := [f19,f21,f22,f177,f198,f189]
def e2114 : List ℕ := [f19,f509,f21,f22,f177,f189]
def e2115 : List ℕ := [f19,f21,f22,f177,f189,f201]
def e2116 : List ℕ := [f19,f21,f22,f510,f177,f189]
def e2117 : List ℕ := [f19,f21,f22,f177,f511,f189]
def e2118 : List ℕ := [f19,f21,f22,f177,f189]
def e2120 : List ℕ := [f19,f289,f22,f177,f24,f189]
def e2121 : List ℕ := [f19,f262,f22,f177,f24,f189]
def e2122 : List ℕ := [f21,f22,f292,f177,f24,f189]
def e2123 : List ℕ := [f19,f21,f292,f177,f24,f189]
def e2124 : List ℕ := [f293,f21,f22,f177,f24,f189]
def e2125 : List ℕ := [f19,f21,f294,f177,f24,f189]
def e2126 : List ℕ := [f19,f21,f22,f119,f24,f189]
def e2127 : List ℕ := [f19,f21,f22,f484,f24,f189]
def e2128 : List ℕ := [f270,f19,f21,f22,f177,f189]
def e2129 : List ℕ := [f19,f21,f22,f177,f342,f189]
def e2130 : List ℕ := [f358,f19,f21,f22,f177,f189]
def e2131 : List ℕ := [f19,f21,f22,f177,f272,f189]
def e2132 : List ℕ := [f19,f22,f192,f177,f24,f189]
def e2133 : List ℕ := [f19,f193,f22,f177,f24,f189]
def e2134 : List ℕ := [f110,f19,f21,f22,f177,f189]
def e2135 : List ℕ := [f19,f21,f22,f177,f189,f164]
def e2136 : List ℕ := [f19,f165,f21,f22,f177,f189]
def e2137 : List ℕ := [f19,f21,f22,f177,f113,f189]
def e2138 : List ℕ := [f19,f21,f22,f167,f24,f189]
def e2139 : List ℕ := [f19,f21,f506,f22,f24,f189]
def e2140 : List ℕ := [f133,f19,f21,f22,f177,f189]
def e2141 : List ℕ := [f19,f21,f22,f177,f189,f134]
def e2142 : List ℕ := [f19,f21,f135,f22,f177,f189]
def e2143 : List ℕ := [f19,f21,f22,f177,f136,f189]
def e2144 : List ℕ := [f19,f21,f22,f177,f24,f171]
def e2145 : List ℕ := [f19,f21,f22,f177,f24,f198]
def e2146 : List ℕ := [f513,f19,f21,f22,f177,f189]
def e2147 : List ℕ := [f19,f21,f22,f514,f177,f189]
def e2148 : List ℕ := [f19,f509,f21,f22,f177,f24]
def e2149 : List ℕ := [f19,f21,f22,f510,f177,f24]
def e2150 : List ℕ := [f19,f203,f21,f22,f177,f189]
def e2151 : List ℕ := [f19,f203,f21,f22,f177,f24]
def e2152 : List ℕ := [f19,f21,f22,f177,f24,f189]
def e2153 : List ℕ := [f19,f20,f21,f22,f177,f189]
def e2154 : List ℕ := [f19,f20,f21,f22,f177,f24,f189]
def e2155 : List ℕ := [f19,f203,f20,f21,f22,f177,f24]
def e2156 : List ℕ := [f19,f20,f21,f22,f177,f204]
def e2157 : List ℕ := [f19,f20,f21,f22,f177,f204,f24]
def e2158 : List ℕ := [f102,f19,f20,f21,f22,f177,f24]
def e2159 : List ℕ := [f19,f20,f22,f192,f177,f24]
def e2160 : List ℕ := [f19,f20,f21,f22,f192,f177,f24]
def e2161 : List ℕ := [f19,f20,f193,f22,f177,f24]
def e2162 : List ℕ := [f19,f20,f193,f21,f22,f177,f24]
def e2163 : List ℕ := [f19,f20,f21,f105,f22,f177,f24]
def e2164 : List ℕ := [f19,f501,f20,f21,f22,f177,f24]
def e2165 : List ℕ := [f19,f20,f21,f22,f177,f415,f24]
def e2166 : List ℕ := [f13,f4,f27,f7]
def e2167 : List ℕ := [f19,f108,f20,f21,f22,f177,f24]
def e2168 : List ℕ := [f19,f20,f21,f22,f502,f177,f24]
def e2169 : List ℕ := [f110,f19,f20,f21,f22,f177,f24]
def e2170 : List ℕ := [f19,f20,f21,f22,f177,f24,f164]
def e2171 : List ℕ := [f19,f20,f165,f21,f22,f177,f24]
def e2172 : List ℕ := [f19,f20,f21,f22,f177,f113,f24]
def e2173 : List ℕ := [f19,f20,f21,f504,f22,f177,f24]
def e2174 : List ℕ := [f19,f20,f21,f22,f167,f24]
def e2175 : List ℕ := [f19,f20,f21,f22,f177,f167,f24]
def e2176 : List ℕ := [f505,f19,f20,f21,f22,f177,f24]
def e2177 : List ℕ := [f19,f20,f21,f506,f22,f24]
def e2178 : List ℕ := [f19,f20,f21,f506,f22,f177,f24]
def e2179 : List ℕ := [f133,f19,f20,f21,f22,f177,f24]
def e2180 : List ℕ := [f19,f20,f21,f22,f177,f134]
def e2181 : List ℕ := [f19,f20,f21,f22,f177,f24,f134]
def e2182 : List ℕ := [f19,f20,f21,f135,f22,f177,f24]
def e2183 : List ℕ := [f19,f20,f21,f22,f177,f136]
def e2184 : List ℕ := [f19,f20,f21,f22,f177,f136,f24]
def e2185 : List ℕ := [f513,f19,f20,f21,f22,f177,f24]
def e2186 : List ℕ := [f19,f20,f21,f22,f177,f24,f201]
def e2187 : List ℕ := [f19,f20,f21,f22,f514,f177,f24]
def e2188 : List ℕ := [f19,f20,f21,f22,f177,f511,f24]
def e2189 : List ℕ := [f19,f20,f21,f22,f177,f24]
def e2190 : List ℕ := [f19,f20,f21,f22,f23,f177,f24]
def e2191 : List ℕ := [f19,f178,f20,f21,f22,f23,f24]
def e2215 : List ℕ := [f18,f19,f20,f21,f22,f179,f24]
def e2216 : List ℕ := [f19,f76,f21,f22,f179,f24]
def e2217 : List ℕ := [f19,f20,f76,f21,f22,f179,f24]
def e2218 : List ℕ := [f75,f19,f20,f21,f22,f179,f24]
def e2219 : List ℕ := [f19,f280,f21,f22,f179,f24]
def e2220 : List ℕ := [f19,f280,f20,f21,f22,f179,f24]
def e2221 : List ℕ := [f97,f19,f20,f21,f22,f179,f24]
def e2222 : List ℕ := [f361,f19,f20,f21,f22,f179,f24]
def e2223 : List ℕ := [f19,f20,f262,f21,f22,f179,f24]
def e2224 : List ℕ := [f291,f19,f20,f21,f22,f179,f24]
def e2225 : List ℕ := [f20,f21,f22,f292,f179,f24]
def e2226 : List ℕ := [f19,f20,f21,f292,f179,f24]
def e2227 : List ℕ := [f19,f20,f21,f22,f292,f179,f24]
def e2228 : List ℕ := [f293,f20,f21,f22,f179,f24]
def e2229 : List ℕ := [f293,f19,f20,f21,f22,f179,f24]
def e2230 : List ℕ := [f19,f20,f21,f294,f179,f24]
def e2231 : List ℕ := [f19,f20,f21,f294,f22,f179,f24]
def e2232 : List ℕ := [f266,f19,f20,f21,f22,f179,f24]
def e2233 : List ℕ := [f19,f20,f21,f22,f520,f24]
def e2234 : List ℕ := [f19,f20,f21,f22,f179,f520,f24]
def e2235 : List ℕ := [f325,f19,f20,f21,f22,f179,f24]
def e2236 : List ℕ := [f19,f20,f21,f22,f121,f24]
def e2237 : List ℕ := [f19,f20,f21,f22,f121,f179,f24]
def e2238 : List ℕ := [f270,f19,f20,f21,f22,f179,f24]
def e2239 : List ℕ := [f358,f19,f20,f21,f22,f179,f24]
def e2240 : List ℕ := [f19,f77,f20,f21,f22,f179,f24]
def e2241 : List ℕ := [f19,f79,f21,f22,f179,f24]
def e2242 : List ℕ := [f19,f79,f20,f21,f22,f179,f24]
def e2243 : List ℕ := [f19,f98,f20,f21,f22,f179,f24]
def e2244 : List ℕ := [f19,f141,f20,f21,f22,f179,f24]
def e2245 : List ℕ := [f19,f21,f22,f155,f179,f24]
def e2246 : List ℕ := [f19,f20,f21,f22,f155,f179,f24]
def e2247 : List ℕ := [f19,f174,f20,f21,f22,f179,f24]
def e2248 : List ℕ := [f19,f20,f21,f175,f22,f179,f24]
def e2249 : List ℕ := [f180,f19,f20,f21,f22,f179,f24]
def e2250 : List ℕ := [f19,f20,f21,f22,f179,f189]
def e2251 : List ℕ := [f19,f20,f21,f22,f179,f24,f189]
def e2252 : List ℕ := [f19,f203,f20,f21,f22,f179,f24]
def e2253 : List ℕ := [f19,f20,f21,f22,f179,f204]
def e2254 : List ℕ := [f19,f20,f21,f22,f179,f204,f24]
def e2255 : List ℕ := [f102,f19,f20,f21,f22,f179,f24]
def e2256 : List ℕ := [f19,f20,f22,f192,f179,f24]
def e2257 : List ℕ := [f19,f20,f21,f22,f192,f179,f24]
def e2258 : List ℕ := [f19,f20,f193,f22,f179,f24]
def e2259 : List ℕ := [f19,f20,f193,f21,f22,f179,f24]
def e2260 : List ℕ := [f19,f20,f21,f105,f22,f179,f24]
def e2261 : List ℕ := [f106,f19,f20,f21,f22,f179,f24]
def e2262 : List ℕ := [f19,f20,f21,f22,f179,f521,f24]
def e2263 : List ℕ := [f13,f4,f515,f7]
def e2264 : List ℕ := [f19,f20,f163,f21,f22,f179,f24]
def e2265 : List ℕ := [f19,f20,f21,f22,f417,f179,f24]
def e2266 : List ℕ := [f110,f19,f20,f21,f22,f179,f24]
def e2267 : List ℕ := [f19,f20,f21,f22,f179,f24,f164]
def e2268 : List ℕ := [f19,f20,f165,f21,f22,f179,f24]
def e2269 : List ℕ := [f19,f20,f21,f22,f179,f113,f24]
def e2270 : List ℕ := [f19,f20,f21,f126,f22,f179,f24]
def e2271 : List ℕ := [f19,f20,f21,f179,f522,f24]
def e2272 : List ℕ := [f19,f20,f21,f22,f522,f24]
def e2273 : List ℕ := [f19,f20,f21,f22,f179,f522,f24]
def e2274 : List ℕ := [f19,f131,f20,f21,f179,f24]
def e2275 : List ℕ := [f19,f131,f20,f21,f22,f179,f24]
def e2276 : List ℕ := [f19,f20,f21,f169,f22,f24]
def e2277 : List ℕ := [f19,f20,f21,f169,f22,f179,f24]
def e2278 : List ℕ := [f133,f19,f20,f21,f22,f179,f24]
def e2279 : List ℕ := [f19,f20,f21,f22,f179,f134]
def e2280 : List ℕ := [f19,f20,f21,f22,f179,f24,f134]
def e2281 : List ℕ := [f19,f20,f21,f135,f22,f179,f24]
def e2282 : List ℕ := [f19,f20,f21,f22,f179,f136]
def e2283 : List ℕ := [f19,f20,f21,f22,f179,f136,f24]
def e2284 : List ℕ := [f137,f19,f20,f21,f22,f179,f24]
def e2285 : List ℕ := [f19,f20,f21,f22,f179,f24,f523]
def e2286 : List ℕ := [f19,f20,f21,f22,f510,f179,f24]
def e2287 : List ℕ := [f19,f20,f21,f22,f179,f140,f24]
def e2288 : List ℕ := [f19,f20,f21,f22,f179,f23,f24]
def e2293 : List ℕ := [f18,f19,f20,f21,f22,f23,f189]
def e2294 : List ℕ := [f19,f20,f76,f21,f22,f23,f189]
def e2295 : List ℕ := [f75,f19,f20,f21,f22,f23,f189]
def e2296 : List ℕ := [f19,f280,f20,f21,f22,f23,f189]
def e2297 : List ℕ := [f97,f19,f20,f21,f22,f23,f189]
def e2298 : List ℕ := [f361,f19,f20,f21,f22,f23,f189]
def e2299 : List ℕ := [f19,f20,f262,f21,f22,f23,f189]
def e2300 : List ℕ := [f291,f19,f20,f21,f22,f23,f189]
def e2301 : List ℕ := [f20,f21,f22,f292,f23,f189]
def e2302 : List ℕ := [f19,f20,f21,f292,f23,f189]
def e2303 : List ℕ := [f19,f20,f21,f22,f292,f23,f189]
def e2304 : List ℕ := [f293,f20,f21,f22,f23,f189]
def e2305 : List ℕ := [f293,f19,f20,f21,f22,f23,f189]
def e2306 : List ℕ := [f19,f20,f21,f294,f23,f189]
def e2307 : List ℕ := [f19,f20,f21,f294,f22,f23,f189]
def e2308 : List ℕ := [f266,f19,f20,f21,f22,f23,f189]
def e2309 : List ℕ := [f19,f20,f21,f22,f298,f189]
def e2310 : List ℕ := [f19,f20,f21,f22,f23,f298,f189]
def e2311 : List ℕ := [f325,f19,f20,f21,f22,f23,f189]
def e2312 : List ℕ := [f19,f20,f21,f22,f269,f189]
def e2313 : List ℕ := [f19,f20,f21,f22,f269,f23,f189]
def e2314 : List ℕ := [f499,f19,f20,f21,f22,f23,f189]
def e2315 : List ℕ := [f19,f20,f21,f22,f23,f189,f123]
def e2316 : List ℕ := [f191,f19,f20,f21,f22,f23,f189]
def e2317 : List ℕ := [f19,f20,f21,f22,f23,f500]
def e2318 : List ℕ := [f19,f20,f21,f22,f23,f500,f189]
def e2319 : List ℕ := [f19,f77,f20,f21,f22,f23,f189]
def e2320 : List ℕ := [f19,f79,f20,f21,f22,f23,f189]
def e2321 : List ℕ := [f19,f98,f20,f21,f22,f23,f189]
def e2322 : List ℕ := [f19,f141,f20,f21,f22,f23,f189]
def e2323 : List ℕ := [f19,f20,f21,f22,f155,f23,f189]
def e2324 : List ℕ := [f19,f174,f20,f21,f22,f23,f189]
def e2325 : List ℕ := [f19,f20,f21,f175,f22,f23,f189]
def e2326 : List ℕ := [f176,f19,f20,f21,f22,f23,f189]
def e2327 : List ℕ := [f19,f21,f22,f23,f177,f189]
def e2328 : List ℕ := [f19,f20,f21,f22,f23,f177,f189]
def e2329 : List ℕ := [f19,f178,f21,f22,f23,f189]
def e2330 : List ℕ := [f19,f178,f20,f21,f22,f23,f189]
def e2331 : List ℕ := [f19,f20,f21,f22,f179,f23,f189]
def e2332 : List ℕ := [f80,f205,f290]
def e2333 : List ℕ := [f19,f21,f22,f23,f204,f189]
def e2334 : List ℕ := [f19,f20,f21,f22,f23,f204]
def e2335 : List ℕ := [f19,f20,f21,f22,f23,f204,f189]
def e2336 : List ℕ := [f102,f19,f20,f21,f22,f23,f189]
def e2337 : List ℕ := [f19,f20,f22,f192,f23,f189]
def e2338 : List ℕ := [f19,f20,f21,f22,f192,f23,f189]
def e2339 : List ℕ := [f19,f20,f193,f22,f23,f189]
def e2340 : List ℕ := [f19,f20,f193,f21,f22,f23,f189]
def e2341 : List ℕ := [f19,f20,f21,f105,f22,f23,f189]
def e2342 : List ℕ := [f106,f19,f20,f21,f22,f23,f189]
def e2343 : List ℕ := [f19,f20,f21,f22,f23,f162,f189]
def e2344 : List ℕ := [f19,f20,f163,f21,f22,f23,f189]
def e2345 : List ℕ := [f19,f20,f21,f22,f109,f23,f189]
def e2346 : List ℕ := [f19,f196,f20,f21,f22,f23,f189]
def e2347 : List ℕ := [f19,f20,f21,f22,f23,f189,f422]
def e2348 : List ℕ := [f19,f112,f20,f21,f22,f23,f189]
def e2349 : List ℕ := [f19,f20,f21,f22,f23,f503,f189]
def e2350 : List ℕ := [f19,f20,f21,f126,f22,f23,f189]
def e2351 : List ℕ := [f90,f91,f366,f380]
def e2352 : List ℕ := [f19,f20,f21,f23,f130,f189]
def e2353 : List ℕ := [f19,f20,f21,f22,f130,f189]
def e2354 : List ℕ := [f19,f20,f21,f22,f23,f130,f189]
def e2355 : List ℕ := [f19,f131,f20,f21,f23,f189]
def e2356 : List ℕ := [f19,f131,f20,f21,f22,f23,f189]
def e2357 : List ℕ := [f19,f20,f21,f132,f22,f189]
def e2358 : List ℕ := [f19,f20,f21,f132,f22,f23,f189]
def e2359 : List ℕ := [f19,f507,f20,f21,f22,f23,f189]
def e2360 : List ℕ := [f19,f20,f21,f22,f23,f171]
def e2361 : List ℕ := [f19,f20,f21,f22,f23,f189,f171]
def e2362 : List ℕ := [f19,f20,f21,f508,f22,f23,f189]
def e2363 : List ℕ := [f19,f20,f21,f22,f23,f198]
def e2364 : List ℕ := [f19,f20,f21,f22,f23,f198,f189]
def e2365 : List ℕ := [f525,f19,f20,f21,f22,f23,f189]
def e2366 : List ℕ := [f19,f20,f21,f22,f23,f189,f201]
def e2367 : List ℕ := [f19,f20,f21,f22,f510,f23,f189]
def e2368 : List ℕ := [f19,f20,f21,f22,f23,f202,f189]
def e2369 : List ℕ := [f19,f20,f21,f22,f23,f189]
def e2370 : List ℕ := [f19,f76,f21,f22,f23,f24,f189]
def e2371 : List ℕ := [f19,f280,f21,f22,f23,f24,f189]
def e2372 : List ℕ := [f20,f21,f22,f292,f23,f24,f189]
def e2373 : List ℕ := [f19,f20,f21,f292,f23,f24,f189]
def e2374 : List ℕ := [f293,f20,f21,f22,f23,f24,f189]
def e2375 : List ℕ := [f19,f20,f21,f294,f23,f24,f189]
def e2376 : List ℕ := [f19,f20,f21,f22,f298,f24,f189]
def e2377 : List ℕ := [f19,f20,f21,f22,f269,f24,f189]
def e2378 : List ℕ := [f270,f19,f20,f21,f22,f23,f189]
def e2379 : List ℕ := [f358,f19,f20,f21,f22,f23,f189]
def e2380 : List ℕ := [f499,f19,f20,f21,f22,f23,f24]
def e2381 : List ℕ := [f191,f19,f20,f21,f22,f23,f24]
def e2382 : List ℕ := [f19,f20,f21,f22,f23,f24,f500]
def e2383 : List ℕ := [f19,f79,f21,f22,f23,f24,f189]
def e2384 : List ℕ := [f19,f21,f155,f23,f24,f189]
def e2385 : List ℕ := [f19,f21,f22,f155,f23,f24,f189]
def e2386 : List ℕ := [f19,f20,f21,f155,f23,f24,f189]
def e2387 : List ℕ := [f19,f174,f21,f22,f23,f24,f189]
def e2388 : List ℕ := [f19,f20,f21,f175,f23,f24,f189]
def e2389 : List ℕ := [f19,f21,f22,f23,f177,f24,f189]
def e2390 : List ℕ := [f19,f178,f21,f22,f23,f24,f189]
def e2391 : List ℕ := [f180,f19,f21,f22,f23,f24,f189]
def e2392 : List ℕ := [f180,f19,f20,f21,f22,f23,f189]
def e2393 : List ℕ := [f19,f203,f20,f21,f22,f23,f189]
def e2394 : List ℕ := [f19,f21,f22,f23,f204,f24,f189]
def e2395 : List ℕ := [f19,f20,f21,f22,f23,f204,f24]
def e2396 : List ℕ := [f19,f20,f22,f192,f23,f24,f189]
def e2397 : List ℕ := [f19,f20,f193,f22,f23,f24,f189]
def e2398 : List ℕ := [f110,f19,f20,f21,f22,f23,f189]
def e2399 : List ℕ := [f19,f20,f21,f22,f23,f189,f164]
def e2400 : List ℕ := [f19,f20,f165,f21,f22,f23,f189]
def e2401 : List ℕ := [f19,f20,f21,f22,f23,f113,f189]
def e2402 : List ℕ := [f19,f196,f20,f21,f22,f23,f24]
def e2403 : List ℕ := [f19,f112,f20,f21,f22,f23,f24]
def e2404 : List ℕ := [f19,f20,f21,f22,f23,f24,f503]
def e2405 : List ℕ := [f19,f20,f21,f23,f130,f24,f189]
def e2406 : List ℕ := [f19,f20,f21,f22,f130,f24,f189]
def e2407 : List ℕ := [f19,f131,f20,f21,f23,f24,f189]
def e2408 : List ℕ := [f19,f20,f21,f132,f22,f24,f189]
def e2409 : List ℕ := [f133,f19,f20,f21,f22,f23,f189]
def e2410 : List ℕ := [f19,f20,f21,f22,f23,f189,f134]
def e2411 : List ℕ := [f19,f20,f21,f135,f22,f23,f189]
def e2412 : List ℕ := [f19,f20,f21,f22,f23,f136,f189]
def e2413 : List ℕ := [f19,f507,f20,f21,f22,f23,f24]
def e2414 : List ℕ := [f19,f20,f21,f22,f23,f24,f171]
def e2415 : List ℕ := [f19,f20,f21,f508,f22,f23,f24]
def e2416 : List ℕ := [f19,f20,f21,f22,f23,f24,f198]
def e2417 : List ℕ := [f137,f19,f20,f21,f22,f23,f189]
def e2418 : List ℕ := [f19,f20,f21,f22,f23,f189,f138]
def e2419 : List ℕ := [f19,f20,f21,f22,f139,f23,f189]
def e2420 : List ℕ := [f19,f20,f21,f22,f23,f140,f189]
def e2421 : List ℕ := [f525,f19,f20,f21,f22,f23,f24]
def e2422 : List ℕ := [f19,f20,f21,f22,f23,f24,f201]
def e2423 : List ℕ := [f19,f20,f21,f22,f510,f23,f24]
def e2424 : List ℕ := [f19,f20,f21,f22,f23,f24,f202]
def e2425 : List ℕ := [f19,f20,f21,f22,f23,f24,f189]
def e2432 : List ℕ := [f18,f19,f20,f21,f22,f23,f204]
def e2433 : List ℕ := [f19,f76,f21,f22,f23,f204]
def e2434 : List ℕ := [f19,f20,f76,f21,f22,f23,f204]
def e2435 : List ℕ := [f75,f19,f20,f21,f22,f23,f204]
def e2436 : List ℕ := [f19,f280,f21,f22,f23,f204]
def e2437 : List ℕ := [f19,f280,f20,f21,f22,f23,f204]
def e2438 : List ℕ := [f97,f19,f20,f21,f22,f23,f204]
def e2439 : List ℕ := [f361,f19,f20,f21,f22,f23,f204]
def e2440 : List ℕ := [f19,f20,f262,f21,f22,f23,f204]
def e2441 : List ℕ := [f291,f19,f20,f21,f22,f23,f204]
def e2442 : List ℕ := [f20,f21,f22,f292,f23,f204]
def e2443 : List ℕ := [f19,f20,f21,f292,f23,f204]
def e2444 : List ℕ := [f19,f20,f21,f22,f292,f23,f204]
def e2445 : List ℕ := [f293,f20,f21,f22,f23,f204]
def e2446 : List ℕ := [f293,f19,f20,f21,f22,f23,f204]
def e2447 : List ℕ := [f19,f20,f21,f294,f23,f204]
def e2448 : List ℕ := [f19,f20,f21,f294,f22,f23,f204]
def e2449 : List ℕ := [f266,f19,f20,f21,f22,f23,f204]
def e2450 : List ℕ := [f19,f20,f21,f22,f298,f204]
def e2451 : List ℕ := [f19,f20,f21,f22,f23,f298,f204]
def e2452 : List ℕ := [f325,f19,f20,f21,f22,f23,f204]
def e2453 : List ℕ := [f19,f20,f21,f22,f269,f204]
def e2454 : List ℕ := [f19,f20,f21,f22,f269,f23,f204]
def e2455 : List ℕ := [f270,f19,f20,f21,f22,f23,f204]
def e2456 : List ℕ := [f19,f20,f21,f22,f23,f529]
def e2457 : List ℕ := [f19,f20,f21,f22,f23,f204,f529]
def e2458 : List ℕ := [f358,f19,f20,f21,f22,f23,f204]
def e2459 : List ℕ := [f19,f20,f21,f22,f23,f125,f204]
def e2460 : List ℕ := [f19,f77,f20,f21,f22,f23,f204]
def e2461 : List ℕ := [f19,f79,f21,f22,f23,f204]
def e2462 : List ℕ := [f19,f79,f20,f21,f22,f23,f204]
def e2463 : List ℕ := [f19,f98,f20,f21,f22,f23,f204]
def e2464 : List ℕ := [f19,f141,f20,f21,f22,f23,f204]
def e2465 : List ℕ := [f19,f21,f22,f155,f23,f204]
def e2466 : List ℕ := [f19,f20,f21,f22,f155,f23,f204]
def e2467 : List ℕ := [f19,f174,f20,f21,f22,f23,f204]
def e2468 : List ℕ := [f19,f20,f21,f175,f22,f23,f204]
def e2469 : List ℕ := [f176,f19,f20,f21,f22,f23,f204]
def e2470 : List ℕ := [f19,f20,f21,f22,f23,f177,f204]
def e2471 : List ℕ := [f19,f178,f20,f21,f22,f23,f204]
def e2472 : List ℕ := [f19,f20,f21,f22,f179,f23,f204]
def e2473 : List ℕ := [f102,f19,f20,f21,f22,f23,f204]
def e2474 : List ℕ := [f19,f20,f22,f192,f23,f204]
def e2475 : List ℕ := [f19,f20,f21,f22,f192,f23,f204]
def e2476 : List ℕ := [f19,f20,f193,f22,f23,f204]
def e2477 : List ℕ := [f19,f20,f193,f21,f22,f23,f204]
def e2478 : List ℕ := [f19,f20,f21,f105,f22,f23,f204]
def e2479 : List ℕ := [f106,f19,f20,f21,f22,f23,f204]
def e2480 : List ℕ := [f19,f20,f21,f22,f23,f162,f204]
def e2481 : List ℕ := [f13,f4,f11,f526]
def e2482 : List ℕ := [f19,f20,f163,f21,f22,f23,f204]
def e2483 : List ℕ := [f19,f20,f21,f22,f109,f23,f204]
def e2484 : List ℕ := [f110,f19,f20,f21,f22,f23,f204]
def e2485 : List ℕ := [f19,f20,f21,f22,f23,f204,f530]
def e2486 : List ℕ := [f19,f20,f165,f21,f22,f23,f204]
def e2487 : List ℕ := [f19,f20,f21,f22,f23,f424,f204]
def e2488 : List ℕ := [f19,f20,f21,f126,f22,f23,f204]
def e2492 : List ℕ := [f19,f20,f21,f23,f130,f204]
def e2493 : List ℕ := [f19,f20,f21,f22,f130,f204]
def e2494 : List ℕ := [f19,f20,f21,f22,f23,f130,f204]
def e2495 : List ℕ := [f19,f131,f20,f21,f23,f204]
def e2496 : List ℕ := [f19,f131,f20,f21,f22,f23,f204]
def e2497 : List ℕ := [f19,f20,f21,f132,f22,f204]
def e2498 : List ℕ := [f19,f20,f21,f132,f22,f23,f204]
def e2499 : List ℕ := [f133,f19,f20,f21,f22,f23,f204]
def e2500 : List ℕ := [f19,f20,f21,f22,f23,f533]
def e2501 : List ℕ := [f19,f20,f21,f22,f23,f204,f533]
def e2502 : List ℕ := [f19,f20,f21,f135,f22,f23,f204]
def e2503 : List ℕ := [f19,f20,f21,f22,f23,f173]
def e2504 : List ℕ := [f19,f20,f21,f22,f23,f173,f204]
def e2505 : List ℕ := [f137,f19,f20,f21,f22,f23,f204]
def e2506 : List ℕ := [f19,f20,f21,f22,f23,f204,f534]
def e2507 : List ℕ := [f19,f20,f21,f22,f139,f23,f204]
def e2508 : List ℕ := [f19,f20,f21,f22,f23,f511,f204]
def e2509 : List ℕ := [f19,f76,f21,f22,f23,f204,f24]
def e2510 : List ℕ := [f19,f280,f21,f22,f23,f204,f24]
def e2511 : List ℕ := [f20,f21,f22,f292,f23,f204,f24]
def e2512 : List ℕ := [f19,f20,f21,f292,f23,f204,f24]
def e2513 : List ℕ := [f293,f20,f21,f22,f23,f204,f24]
def e2514 : List ℕ := [f19,f20,f21,f294,f23,f204,f24]
def e2515 : List ℕ := [f19,f20,f21,f22,f298,f204,f24]
def e2516 : List ℕ := [f19,f20,f21,f22,f269,f204,f24]
def e2517 : List ℕ := [f19,f20,f21,f22,f23,f24,f529]
def e2518 : List ℕ := [f19,f79,f21,f22,f23,f204,f24]
def e2519 : List ℕ := [f19,f21,f22,f155,f23,f204,f24]
def e2520 : List ℕ := [f19,f20,f21,f155,f23,f204,f24]
def e2521 : List ℕ := [f19,f20,f21,f175,f23,f204,f24]
def e2522 : List ℕ := [f176,f19,f21,f22,f23,f204,f24]
def e2523 : List ℕ := [f33,f34,f37,f83]
def e2524 : List ℕ := [f19,f21,f22,f179,f23,f204,f24]
def e2525 : List ℕ := [f180,f19,f20,f21,f22,f23,f204]
def e2526 : List ℕ := [f19,f203,f21,f22,f23,f204,f24]
def e2527 : List ℕ := [f19,f203,f20,f21,f22,f23,f204]
def e2528 : List ℕ := [f19,f20,f22,f192,f23,f204,f24]
def e2529 : List ℕ := [f19,f20,f193,f22,f23,f204,f24]
def e2530 : List ℕ := [f13,f4,f11,f526,f7]
def e2531 : List ℕ := [f19,f20,f21,f22,f23,f24,f530]
def e2532 : List ℕ := [f19,f20,f21,f22,f23,f204,f164]
def e2533 : List ℕ := [f19,f20,f21,f22,f23,f113,f204]
def e2534 : List ℕ := [f19,f20,f21,f23,f130,f204,f24]
def e2535 : List ℕ := [f19,f20,f21,f22,f130,f204,f24]
def e2536 : List ℕ := [f19,f131,f20,f21,f23,f204,f24]
def e2537 : List ℕ := [f19,f20,f21,f132,f22,f204,f24]
def e2538 : List ℕ := [f19,f20,f21,f22,f23,f24,f533]
def e2539 : List ℕ := [f19,f20,f21,f22,f23,f173,f24]
def e2540 : List ℕ := [f19,f20,f21,f22,f23,f204,f134]
def e2541 : List ℕ := [f19,f20,f21,f22,f23,f204,f136]
def e2542 : List ℕ := [f19,f20,f21,f22,f23,f24,f534]
def e2543 : List ℕ := [f19,f20,f21,f22,f23,f511,f24]
def e2544 : List ℕ := [f19,f20,f21,f22,f23,f204,f138]
def e2545 : List ℕ := [f19,f20,f21,f22,f23,f140,f204]
def e2546 : List ℕ := [f102,f19,f20,f21,f22,f23,f24]
def e2547 : List ℕ := [f19,f20,f22,f192,f23,f24]
def e2548 : List ℕ := [f19,f20,f21,f22,f192,f23,f24]
def e2549 : List ℕ := [f19,f20,f193,f22,f23,f24]
def e2550 : List ℕ := [f19,f20,f193,f21,f22,f23,f24]
def e2551 : List ℕ := [f19,f20,f21,f105,f22,f23,f24]
def e2552 : List ℕ := [f106,f19,f20,f21,f22,f23,f24]
def e2553 : List ℕ := [f19,f76,f21,f22,f23,f162,f24]
def e2554 : List ℕ := [f19,f280,f21,f22,f23,f162,f24]
def e2555 : List ℕ := [f19,f20,f262,f22,f23,f162,f24]
def e2556 : List ℕ := [f20,f21,f22,f292,f23,f162,f24]
def e2557 : List ℕ := [f19,f20,f21,f292,f23,f162,f24]
def e2558 : List ℕ := [f293,f20,f21,f22,f23,f162,f24]
def e2559 : List ℕ := [f19,f20,f21,f294,f23,f162,f24]
def e2560 : List ℕ := [f19,f20,f21,f22,f298,f162,f24]
def e2561 : List ℕ := [f19,f20,f21,f22,f269,f162,f24]
def e2562 : List ℕ := [f535,f19,f20,f21,f22,f23,f24]
def e2563 : List ℕ := [f536,f19,f20,f21,f22,f23,f24]
def e2564 : List ℕ := [f13,f4,f6,f11,f7]
def e2565 : List ℕ := [f19,f20,f21,f22,f23,f537,f24]
def e2566 : List ℕ := [f19,f78,f22,f23,f162,f24]
def e2567 : List ℕ := [f19,f21,f78,f22,f23,f162,f24]
def e2571 : List ℕ := [f19,f79,f21,f22,f23,f162,f24]
def e2572 : List ℕ := [f19,f98,f20,f22,f23,f162,f24]
def e2573 : List ℕ := [f19,f20,f21,f155,f23,f162,f24]
def e2574 : List ℕ := [f19,f20,f21,f175,f23,f162,f24]
def e2575 : List ℕ := [f19,f20,f21,f22,f177,f162,f24]
def e2576 : List ℕ := [f19,f20,f21,f22,f179,f162,f24]
def e2577 : List ℕ := [f19,f539,f20,f21,f22,f23,f24]
def e2578 : List ℕ := [f19,f540,f20,f21,f22,f23,f24]
def e2579 : List ℕ := [f19,f20,f21,f22,f23,f541,f24]
def e2580 : List ℕ := [f19,f20,f22,f192,f23,f162,f24]
def e2581 : List ℕ := [f19,f20,f193,f22,f23,f162,f24]
def e2582 : List ℕ := [f106,f19,f20,f22,f23,f162,f24]
def e2583 : List ℕ := [f106,f19,f20,f21,f22,f162,f24]
def e2584 : List ℕ := [f19,f20,f163,f21,f22,f162,f24]
def e2585 : List ℕ := [f19,f20,f22,f109,f23,f162,f24]
def e2586 : List ℕ := [f19,f20,f21,f22,f109,f23,f24]
def e2587 : List ℕ := [f249,f250,f251,f256,f365]
def e2588 : List ℕ := [f249,f251,f256,f428]
def e2589 : List ℕ := [f249,f250,f251,f256,f428]
def e2590 : List ℕ := [f249,f251,f256,f365,f428]
def e2591 : List ℕ := [f249,f250,f251,f256,f365,f428]
def e2592 : List ℕ := [f19,f20,f22,f23,f162,f24,f164]
def e2593 : List ℕ := [f19,f20,f165,f22,f23,f162,f24]
def e2594 : List ℕ := [f19,f20,f21,f130,f162,f24]
def e2595 : List ℕ := [f19,f20,f21,f23,f130,f162,f24]
def e2596 : List ℕ := [f19,f20,f21,f22,f130,f162,f24]
def e2597 : List ℕ := [f19,f131,f20,f21,f23,f162,f24]
def e2598 : List ℕ := [f19,f20,f21,f132,f22,f162,f24]
def e2599 : List ℕ := [f19,f20,f21,f542,f22,f23,f24]
def e2600 : List ℕ := [f19,f20,f21,f22,f23,f543,f24]
def e2601 : List ℕ := [f19,f544,f20,f21,f22,f23,f24]
def e2602 : List ℕ := [f19,f20,f21,f545,f22,f23,f24]
def e2603 : List ℕ := [f19,f20,f21,f22,f23,f162,f134]
def e2604 : List ℕ := [f19,f20,f21,f22,f23,f162,f136]
def e2605 : List ℕ := [f19,f20,f163,f21,f22,f23,f24]
def e2606 : List ℕ := [f19,f20,f21,f22,f162,f24,f138]
def e2607 : List ℕ := [f19,f20,f21,f22,f139,f162,f24]
def e2608 : List ℕ := [f546,f19,f20,f21,f22,f23]
def e2609 : List ℕ := [f546,f19,f20,f21,f22,f23,f24]
def e2610 : List ℕ := [f546,f19,f20,f21,f22,f23,f162]
def e2611 : List ℕ := [f1,f2,f3,f547]
def e2612 : List ℕ := [f19,f20,f21,f22,f23,f24,f548]
def e2613 : List ℕ := [f19,f20,f21,f22,f23,f549]
def e2614 : List ℕ := [f1,f2,f550]
def e2615 : List ℕ := [f1,f2,f550,f3]
def e2616 : List ℕ := [f19,f20,f21,f22,f23,f549,f24]
def e2617 : List ℕ := [f19,f20,f21,f22,f23,f549,f162]
def e2618 : List ℕ := [f19,f20,f21,f22,f23,f551,f24]
def e2619 : List ℕ := [f19,f20,f21,f22,f23,f162,f24]
def e2620 : List ℕ := [f19,f76,f21,f22,f23,f24,f164]
def e2621 : List ℕ := [f19,f280,f21,f22,f23,f24,f164]
def e2622 : List ℕ := [f19,f20,f262,f22,f23,f24,f164]
def e2623 : List ℕ := [f20,f21,f22,f292,f23,f24,f164]
def e2625 : List ℕ := [f19,f20,f21,f292,f23,f24,f164]
def e2626 : List ℕ := [f293,f20,f21,f22,f23,f24,f164]
def e2632 : List ℕ := [f19,f20,f21,f294,f23,f24,f164]
def e2633 : List ℕ := [f19,f20,f21,f22,f298,f24,f164]
def e2634 : List ℕ := [f19,f20,f21,f22,f269,f24,f164]
def e2635 : List ℕ := [f553,f19,f20,f21,f22,f23,f24]
def e2636 : List ℕ := [f554,f19,f20,f21,f22,f23,f24]
def e2637 : List ℕ := [f4,f11,f7,f555]
def e2638 : List ℕ := [f13,f4,f11,f7,f555]
def e2639 : List ℕ := [f19,f20,f21,f22,f23,f24,f556]
def e2640 : List ℕ := [f40,f63,f61,f44,f209]
def e2641 : List ℕ := [f19,f78,f22,f23,f24,f164]
def e2642 : List ℕ := [f19,f21,f78,f22,f23,f24,f164]
def e2643 : List ℕ := [f19,f79,f21,f22,f23,f24,f164]
def e2644 : List ℕ := [f19,f98,f20,f22,f23,f24,f164]
def e2645 : List ℕ := [f19,f20,f21,f155,f23,f24,f164]
def e2646 : List ℕ := [f19,f20,f21,f175,f23,f24,f164]
def e2647 : List ℕ := [f19,f557,f20,f21,f22,f23,f24]
def e2648 : List ℕ := [f19,f558,f20,f21,f22,f23,f24]
def e2649 : List ℕ := [f19,f20,f21,f22,f23,f24,f559]
def e2650 : List ℕ := [f19,f20,f22,f192,f23,f24,f164]
def e2651 : List ℕ := [f19,f20,f193,f22,f23,f24,f164]
def e2652 : List ℕ := [f19,f20,f163,f22,f23,f24,f164]
def e2653 : List ℕ := [f82,f13,f11,f7,f200]
def e2654 : List ℕ := [f110,f19,f20,f22,f23,f24,f164]
def e2655 : List ℕ := [f110,f19,f20,f21,f22,f23,f164]
def e2656 : List ℕ := [f19,f20,f165,f21,f22,f23,f164]
def e2657 : List ℕ := [f19,f20,f22,f23,f113,f24,f164]
def e2658 : List ℕ := [f19,f20,f21,f22,f23,f113,f24]
def e2663 : List ℕ := [f40,f41,f42,f563,f44]
def e2664 : List ℕ := [f40,f41,f42,f563,f44,f421]
def e2665 : List ℕ := [f19,f20,f21,f23,f130,f24,f164]
def e2666 : List ℕ := [f19,f20,f21,f22,f130,f24,f164]
def e2674 : List ℕ := [f19,f131,f20,f21,f23,f24,f164]
def e2675 : List ℕ := [f19,f20,f21,f132,f22,f24,f164]
def e2676 : List ℕ := [f19,f20,f21,f22,f23,f164,f134]
def e2677 : List ℕ := [f19,f20,f21,f22,f23,f136,f164]
def e2678 : List ℕ := [f564,f19,f20,f21,f23,f24]
def e2679 : List ℕ := [f26,f33,f197,f37]
def e2680 : List ℕ := [f564,f19,f20,f21,f23,f24,f164]
def e2681 : List ℕ := [f564,f19,f20,f21,f22,f23,f24]
def e2682 : List ℕ := [f19,f20,f21,f22,f23,f24,f565]
def e2683 : List ℕ := [f19,f20,f21,f566,f22,f23,f24]
def e2684 : List ℕ := [f33,f34,f197,f37]
def e2685 : List ℕ := [f19,f20,f21,f23,f24,f567]
def e2686 : List ℕ := [f19,f20,f21,f23,f24,f567,f164]
def e2687 : List ℕ := [f19,f20,f21,f22,f23,f24,f567]
def e2694 : List ℕ := [f40,f41,f42,f43,f570]
def e2695 : List ℕ := [f40,f41,f42,f43,f421,f570]
def e2696 : List ℕ := [f19,f20,f21,f22,f23,f164,f138]
def e2697 : List ℕ := [f13,f4,f199,f7]
def e2698 : List ℕ := [f13,f4,f11,f199,f7]
def e2699 : List ℕ := [f19,f20,f21,f22,f23,f140,f164]
def e2700 : List ℕ := [f571,f19,f20,f21,f22,f24]
def e2701 : List ℕ := [f571,f19,f20,f21,f22,f24,f164]
def e2702 : List ℕ := [f571,f19,f20,f21,f22,f23,f24]
def e2703 : List ℕ := [f19,f20,f21,f22,f572,f23,f24]
def e2704 : List ℕ := [f19,f20,f21,f22,f24,f573]
def e2705 : List ℕ := [f19,f20,f21,f22,f24,f573,f164]
def e2706 : List ℕ := [f1,f3,f574]
def e2707 : List ℕ := [f1,f2,f3,f574]
def e2708 : List ℕ := [f19,f20,f21,f22,f23,f24,f573]
def e2709 : List ℕ := [f19,f20,f21,f22,f23,f24,f164]
def e2714 : List ℕ := [f19,f76,f21,f22,f23,f113,f24]
def e2715 : List ℕ := [f19,f280,f21,f22,f23,f113,f24]
def e2716 : List ℕ := [f20,f21,f22,f292,f23,f113,f24]
def e2717 : List ℕ := [f33,f197,f37,f363]
def e2718 : List ℕ := [f19,f20,f21,f292,f23,f113,f24]
def e2719 : List ℕ := [f293,f20,f21,f22,f23,f113,f24]
def e2720 : List ℕ := [f33,f197,f552,f37]
def e2721 : List ℕ := [f19,f20,f21,f294,f23,f113,f24]
def e2722 : List ℕ := [f19,f20,f21,f22,f298,f113,f24]
def e2723 : List ℕ := [f19,f20,f21,f22,f269,f113,f24]
def e2724 : List ℕ := [f19,f20,f21,f22,f23,f24,f576]
def e2725 : List ℕ := [f19,f21,f78,f22,f23,f113,f24]
def e2726 : List ℕ := [f33,f532,f34,f83]
def e2727 : List ℕ := [f19,f79,f21,f22,f23,f113,f24]
def e2728 : List ℕ := [f19,f20,f21,f155,f23,f113,f24]
def e2729 : List ℕ := [f19,f20,f21,f175,f23,f113,f24]
def e2730 : List ℕ := [f19,f20,f21,f22,f23,f24,f577]
def e2731 : List ℕ := [f19,f20,f22,f192,f23,f113,f24]
def e2732 : List ℕ := [f19,f20,f193,f22,f23,f113,f24]
def e2733 : List ℕ := [f106,f19,f20,f22,f23,f113,f24]
def e2734 : List ℕ := [f19,f20,f22,f109,f23,f113,f24]
def e2735 : List ℕ := [f110,f19,f20,f21,f22,f23,f113]
def e2736 : List ℕ := [f210,f2,f211,f3]
def e2737 : List ℕ := [f19,f20,f165,f22,f23,f113,f24]
def e2738 : List ℕ := [f210,f1,f2,f211]
def e2739 : List ℕ := [f19,f20,f165,f21,f22,f23,f113]
def e2740 : List ℕ := [f19,f20,f21,f23,f130,f113,f24]
def e2741 : List ℕ := [f19,f20,f21,f22,f130,f113,f24]
def e2742 : List ℕ := [f33,f532,f197,f37]
def e2743 : List ℕ := [f19,f131,f20,f21,f23,f113,f24]
def e2744 : List ℕ := [f19,f20,f21,f132,f22,f113,f24]
def e2745 : List ℕ := [f19,f20,f21,f22,f23,f24,f578]
def e2746 : List ℕ := [f19,f20,f21,f22,f23,f579,f24]
def e2747 : List ℕ := [f19,f20,f21,f22,f23,f113,f134]
def e2748 : List ℕ := [f19,f20,f21,f22,f23,f113,f136]
def e2749 : List ℕ := [f1,f2,f3,f580]
def e2750 : List ℕ := [f19,f20,f21,f22,f23,f24,f581]
def e2751 : List ℕ := [f19,f20,f21,f22,f23,f113,f138]
def e2752 : List ℕ := [f1,f2,f461,f211]
def e2753 : List ℕ := [f19,f20,f21,f22,f23,f140,f113]
def e2754 : List ℕ := [f19,f20,f21,f126,f22,f23,f24]
def e2755 : List ℕ := [f19,f20,f21,f23,f130,f24]
def e2756 : List ℕ := [f19,f20,f21,f22,f130,f24]
def e2757 : List ℕ := [f19,f20,f21,f22,f23,f130,f24]
def e2758 : List ℕ := [f19,f131,f20,f21,f23,f24]
def e2759 : List ℕ := [f19,f131,f20,f21,f22,f23,f24]
def e2760 : List ℕ := [f19,f20,f21,f132,f22,f24]
def e2761 : List ℕ := [f19,f20,f21,f132,f22,f23,f24]
def e2762 : List ℕ := [f19,f20,f21,f22,f23,f134]
def e2763 : List ℕ := [f19,f20,f21,f22,f23,f24,f134]
def e2764 : List ℕ := [f19,f20,f21,f22,f23,f136]
def e2765 : List ℕ := [f19,f20,f21,f22,f23,f136,f24]
def e2766 : List ℕ := [f19,f20,f21,f22,f23,f24,f138]
def e2767 : List ℕ := [f19,f20,f21,f22,f23,f140,f24]
def e2768 : List ℕ := [f19,f20,f21,f22,f23,f24]
theorem b0:B 12 3 e0:=viaSmall (by decide +kernel) (by decide)
theorem b16:B 20 4 e9:=viaSmall (by decide +kernel) (by decide)
theorem b19:B 20 3 e12:=viaSmall (by decide +kernel) (by decide)
theorem b21:B 20 3 e14:=viaPerm pc11_0 pci11_0 b19 (by decide +kernel) (by decide +kernel)
theorem b26:B 20 3 e12:=viaSmall (by decide +kernel) (by decide)
theorem b28:B 20 3 e14:=viaPerm pc15_0 pci15_0 b26 (by decide +kernel) (by decide +kernel)
theorem b30:B 12 3 e16:=viaSmall (by decide +kernel) (by decide)
theorem w31:W 12 3 e16:=widen (by decide +kernel) b30
theorem b32:B 89 7 e17:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b34:B 20 4 e19:=viaSmall (by decide +kernel) (by decide)
theorem b35:B 20 4 e20:=viaSmall (by decide +kernel) (by decide)
theorem b37:B 20 4 e22:=viaPerm pc7_1 pci7_1 b34 (by decide +kernel) (by decide +kernel)
theorem b38:B 20 4 e23:=viaPerm pc7_1 pci7_1 b35 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b49:B 40 5 e33:=viaSmall (by decide +kernel) (by decide)
theorem b90:B 20 3 e74:=viaSmall (by decide +kernel) (by decide)
theorem b91:B 89 6 e75:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b92:B 89 6 e76:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b93:B 12 2 e16:=viaSmall (by decide +kernel) (by decide)
theorem w94:W 12 2 e16:=widen (by decide +kernel) b93
theorem b95:B 89 6 e77:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b96:B 89 6 e78:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b97:B 89 6 e79:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b98:B 89 6 e80:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b99:B 89 6 e81:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b100:B 89 6 e82:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b107:B 89 5 e89:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b108:B 89 5 e90:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b109:B 20 2 e74:=viaSmall (by decide +kernel) (by decide)
theorem w110:W 20 2 e74:=widen (by decide +kernel) b109
theorem b111:B 89 5 e91:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b112:B 89 5 e92:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b113:B 89 5 e93:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b114:B 89 5 e94:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b115:B 89 5 e95:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b116:B 89 5 e96:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b117:B 89 5 e97:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b118:B 89 5 e98:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b119:B 89 5 e99:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem w120:W 20 3 e74:=widen (by decide +kernel) b90
theorem b121:B 89 5 e100:=viaCut pjt_11 w120 (by decide) (by decide +kernel) (by decide +kernel)
theorem b122:B 89 5 e101:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b123:B 89 5 e102:=viaCut pjt_11 w120 (by decide) (by decide +kernel) (by decide +kernel)
theorem b124:B 89 5 e103:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b125:B 89 5 e104:=viaCut pjt_11 w120 (by decide) (by decide +kernel) (by decide +kernel)
theorem b126:B 89 5 e105:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b127:B 89 5 e106:=viaCut pjt_11 w120 (by decide) (by decide +kernel) (by decide +kernel)
theorem b128:B 89 5 e107:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b129:B 89 5 e108:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b130:B 89 5 e109:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b131:B 89 5 e110:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b132:B 89 5 e111:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b133:B 89 5 e112:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b134:B 89 5 e113:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b135:B 89 5 e114:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b136:B 89 5 e115:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b137:B 89 5 e116:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b138:B 89 5 e117:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b139:B 89 5 e118:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b140:B 89 5 e119:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b141:B 89 5 e120:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b142:B 89 5 e121:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b143:B 89 5 e122:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b144:B 89 5 e123:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b145:B 16 3 e124:=viaSmall (by decide +kernel) (by decide)
theorem b147:B 20 4 e126:=viaSmall (by decide +kernel) (by decide)
theorem w148:W 20 4 e126:=widen (by decide +kernel) b147
theorem b149:B 89 5 e127:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b150:B 89 5 e128:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b151:B 89 5 e129:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b152:B 89 5 e130:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b153:B 89 5 e131:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b154:B 89 5 e132:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b155:B 89 5 e133:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b156:B 89 5 e134:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b157:B 89 5 e135:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b158:B 89 5 e136:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b159:B 89 5 e137:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b160:B 89 5 e138:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b161:B 89 5 e139:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b162:B 20 3 e126:=viaSmall (by decide +kernel) (by decide)
theorem w163:W 20 3 e126:=widen (by decide +kernel) b162
theorem b164:B 89 5 e140:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b165:B 89 5 e141:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b166:B 89 5 e142:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b167:B 89 5 e143:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b168:B 89 6 e144:=viaBranch (ws:=[e89,e90,e91,e92,e93,e94,e95,e96,e97,e98,e99,e100,e101,e102,e103,e104,e105,e106,e107,e108,e109,e110,e111,e112,e113,e114,e115,e116,e117,e118,e119,e120,e121,e122,e123,e127,e128,e129,e130,e131,e132,e133,e134,e135,e136,e137,e138,e139,e140,e141,e142,e143]) (consBan b107 (consBan b108 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b169:B 89 6 e145:=viaCut pjt_11 w120 (by decide) (by decide +kernel) (by decide +kernel)
theorem b170:B 89 6 e146:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b171:B 89 6 e147:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b172:B 89 6 e148:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b180:B 89 5 e155:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b181:B 89 5 e156:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b182:B 89 5 e157:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b183:B 89 5 e158:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b184:B 89 5 e159:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b185:B 89 5 e160:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b186:B 89 5 e161:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b187:B 89 5 e162:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b188:B 89 5 e163:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b189:B 89 5 e164:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b190:B 89 5 e165:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b191:B 89 5 e166:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b192:B 89 5 e167:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b193:B 89 5 e168:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b194:B 89 5 e169:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b195:B 89 5 e170:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b196:B 89 5 e171:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b197:B 89 5 e172:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b198:B 89 5 e173:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b199:B 89 5 e174:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b200:B 89 5 e175:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b201:B 89 5 e176:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b202:B 89 5 e177:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b203:B 89 5 e178:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b204:B 16 3 e179:=viaSmall (by decide +kernel) (by decide)
theorem w205:W 16 3 e179:=widen (by decide +kernel) b204
theorem b206:B 89 5 e180:=viaCut pjt_8 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b207:B 89 5 e181:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b208:B 89 5 e182:=viaCut pjt_8 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b209:B 89 5 e183:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b210:B 89 5 e184:=viaCut pjt_8 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b211:B 24 4 e185:=viaSmall (by decide +kernel) (by decide)
theorem w212:W 24 4 e185:=widen (by decide +kernel) b211
theorem b213:B 89 5 e186:=viaCut pjt_3 w212 (by decide) (by decide +kernel) (by decide +kernel)
theorem b214:B 89 5 e187:=viaCut pjt_8 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b215:B 89 5 e188:=viaCut pjt_3 w212 (by decide) (by decide +kernel) (by decide +kernel)
theorem b216:B 89 5 e189:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b217:B 89 5 e190:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b218:B 89 5 e191:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b219:B 89 5 e192:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b220:B 89 5 e193:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b221:B 89 5 e194:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b222:B 89 5 e195:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b223:B 89 5 e196:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b224:B 89 5 e197:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b225:B 89 5 e198:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b226:B 89 5 e199:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b227:B 89 5 e200:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b228:B 89 5 e201:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b229:B 89 5 e202:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b230:B 89 6 e203:=viaBranch (ws:=[e155,e156,e157,e158,e159,e160,e161,e162,e163,e164,e165,e166,e167,e168,e169,e170,e171,e172,e173,e174,e175,e176,e177,e178,e180,e181,e182,e183,e184,e186,e187,e188,e189,e190,e191,e192,e193,e194,e195,e196,e197,e198,e199,e200,e201,e202]) (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b231:B 89 6 e204:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b232:B 89 6 e205:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b233:B 89 6 e206:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b234:B 89 6 e207:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b235:B 89 6 e208:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b236:B 89 6 e209:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b237:B 89 6 e210:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b238:B 89 6 e211:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b239:B 89 6 e212:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b240:B 89 6 e213:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b241:B 89 6 e214:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b242:B 89 6 e215:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b243:B 89 6 e216:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b244:B 89 6 e217:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b258:B 89 5 e225:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b259:B 89 5 e226:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b260:B 89 5 e227:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b261:B 89 5 e228:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b262:B 89 5 e229:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b263:B 89 5 e230:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b264:B 89 5 e231:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b265:B 89 5 e232:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b266:B 89 5 e233:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b267:B 89 5 e234:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b268:B 89 5 e235:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b269:B 89 5 e236:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b270:B 16 3 e237:=viaSmall (by decide +kernel) (by decide)
theorem w271:W 16 3 e237:=widen (by decide +kernel) b270
theorem b272:B 89 5 e238:=viaCut pjt_12 w271 (by decide) (by decide +kernel) (by decide +kernel)
theorem b273:B 40 4 e239:=viaSmall (by decide +kernel) (by decide)
theorem w274:W 40 4 e239:=widen (by decide +kernel) b273
theorem b275:B 89 5 e240:=viaCut pjt_1 w274 (by decide) (by decide +kernel) (by decide +kernel)
theorem b276:B 89 5 e241:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b277:B 89 5 e242:=viaCut pjt_11 w110 (by decide) (by decide +kernel) (by decide +kernel)
theorem b278:B 16 3 e243:=viaSmall (by decide +kernel) (by decide)
theorem w279:W 16 3 e243:=widen (by decide +kernel) b278
theorem b280:B 89 5 e244:=viaCut pjt_16 w279 (by decide) (by decide +kernel) (by decide +kernel)
theorem b281:B 89 5 e245:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b282:B 89 5 e246:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b283:B 89 5 e247:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b284:B 89 5 e248:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b285:B 89 5 e249:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b286:B 89 5 e250:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b287:B 89 5 e251:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b288:B 89 5 e252:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b289:B 20 3 e253:=viaSmall (by decide +kernel) (by decide)
theorem w290:W 20 3 e253:=widen (by decide +kernel) b289
theorem b291:B 89 5 e254:=viaCut pjt_11 w290 (by decide) (by decide +kernel) (by decide +kernel)
theorem b292:B 89 5 e255:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b293:B 89 5 e256:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b294:B 89 5 e257:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b295:B 89 5 e258:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b296:B 89 6 e259:=viaBranch (ws:=[e225,e226,e227,e228,e229,e230,e231,e232,e233,e234,e235,e236,e238,e240,e241,e242,e244,e245,e246,e247,e248,e249,e250,e251,e252,e254,e255,e256,e257,e258]) (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b272 (consBan b275 (consBan b276 (consBan b277 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b291 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (nilBan _ _))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b297:B 89 6 e260:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b298:B 89 6 e258:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b299:B 89 6 e261:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b300:B 89 6 e262:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b301:B 89 6 e263:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b302:B 89 6 e264:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b303:B 89 6 e265:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b304:B 89 6 e266:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b305:B 89 6 e267:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b306:B 89 6 e268:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b307:B 89 6 e269:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b308:B 89 6 e270:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b309:B 89 6 e271:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b310:B 89 6 e272:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b311:B 89 6 e273:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b312:B 89 6 e274:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b313:B 89 6 e275:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b314:B 89 6 e276:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b315:B 89 6 e277:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b316:B 89 6 e278:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b317:B 89 6 e279:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b318:B 89 6 e280:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b319:B 89 6 e281:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b320:B 89 6 e282:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b321:B 89 6 e283:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b322:B 89 6 e284:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b323:B 89 6 e285:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b324:B 89 6 e286:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b325:B 89 6 e287:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b326:B 89 6 e288:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b327:B 89 6 e289:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b328:B 89 6 e290:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b329:B 89 6 e291:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b330:B 89 6 e292:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b331:B 89 6 e293:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b332:B 89 6 e294:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b333:B 6 2 e83:=viaSmall (by decide +kernel) (by decide)
theorem b334:B 6 2 e83:=viaSmall (by decide +kernel) (by decide)
theorem b336:B 16 3 e296:=viaSmall (by decide +kernel) (by decide)
theorem b337:B 16 3 e297:=viaSmall (by decide +kernel) (by decide)
theorem w338:W 16 3 e297:=viaSub (ws:=[e296,e297]) (consBan b336 (consBan b337 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b339:B 89 6 e298:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b341:B 20 4 e299:=viaSmall (by decide +kernel) (by decide)
theorem b346:B 40 5 e304:=viaSmall (by decide +kernel) (by decide)
theorem b347:B 40 5 e305:=viaSmall (by decide +kernel) (by decide)
theorem b348:B 40 5 e306:=viaSmall (by decide +kernel) (by decide)
theorem w349:W 40 5 e306:=viaSub (ws:=[e304,e305,e306]) (consBan b346 (consBan b347 (consBan b348 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b350:B 89 6 e307:=viaCut pjt_1 w349 (by decide) (by decide +kernel) (by decide +kernel)
theorem b351:B 12 3 e308:=viaPerm pc18_0 pci18_0 b0 (by decide +kernel) (by decide +kernel)
theorem w352:W 12 3 e308:=viaSub (ws:=[e16,e308]) (consBan b30 (consBan b351 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b353:B 89 6 e309:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b354:B 12 3 e310:=viaPerm pc18_3 pci18_3 b0 (by decide +kernel) (by decide +kernel)
theorem w355:W 12 3 e310:=viaSub (ws:=[e16,e310]) (consBan b30 (consBan b354 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b356:B 89 6 e311:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b357:B 89 6 e312:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b358:B 89 6 e313:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b359:B 89 6 e314:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b360:B 89 6 e315:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b361:B 89 6 e316:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b362:B 89 6 e317:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b363:B 89 6 e318:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b364:B 89 6 e319:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b365:B 89 6 e320:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b366:B 89 6 e321:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b367:B 89 6 e322:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b368:B 89 6 e323:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b369:B 89 6 e324:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b370:B 89 6 e325:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b371:B 89 6 e326:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b372:B 89 6 e327:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b373:B 89 6 e328:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b374:B 89 6 e329:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b375:B 89 7 e330:=viaBranch (ws:=[e75,e76,e77,e78,e79,e80,e81,e82,e144,e145,e146,e147,e148,e203,e204,e205,e206,e207,e208,e209,e210,e211,e212,e213,e214,e215,e216,e217,e259,e260,e258,e261,e262,e263,e264,e265,e266,e267,e268,e269,e270,e271,e272,e273,e274,e275,e276,e277,e278,e279,e280,e281,e282,e283,e284,e285,e286,e287,e288,e289,e290,e291,e292,e293,e294,e298,e307,e309,e311,e312,e313,e314,e315,e316,e317,e318,e319,e320,e321,e322,e323,e324,e325,e326,e327,e328,e329]) (consBan b91 (consBan b92 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b241 (consBan b242 (consBan b243 (consBan b244 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b339 (consBan b350 (consBan b353 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b378:B 40 5 e332:=viaSmall (by decide +kernel) (by decide)
theorem b379:B 40 5 e333:=viaSmall (by decide +kernel) (by decide)
theorem b380:B 40 5 e334:=viaSmall (by decide +kernel) (by decide)
theorem b381:B 40 5 e335:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b382:B 40 5 e336:=viaSmall (by decide +kernel) (by decide)
theorem b383:B 40 5 e337:=viaSmall (by decide +kernel) (by decide)
theorem b384:B 40 5 e338:=viaSmall (by decide +kernel) (by decide)
theorem b385:B 40 5 e339:=viaSmall (by decide +kernel) (by decide)
theorem b386:B 40 5 e340:=viaSmall (by decide +kernel) (by decide)
theorem b387:B 40 5 e341:=viaSmall (by decide +kernel) (by decide)
theorem b388:B 40 5 e342:=viaSmall (by decide +kernel) (by decide)
theorem b389:B 40 5 e343:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b390:B 40 5 e344:=viaSmall (by decide +kernel) (by decide)
theorem b391:B 40 5 e345:=viaSmall (by decide +kernel) (by decide)
theorem b392:B 40 5 e346:=viaSmall (by decide +kernel) (by decide)
theorem b393:B 40 5 e347:=viaPerm pc1_0 pci1_0 b387 (by decide +kernel) (by decide +kernel)
theorem b394:B 40 5 e348:=viaPerm pc1_0 pci1_0 b388 (by decide +kernel) (by decide +kernel)
theorem b395:B 40 5 e349:=viaPerm pc1_0 pci1_0 b389 (by decide +kernel) (by decide +kernel)
theorem b396:B 40 5 e350:=viaPerm pc1_0 pci1_0 b390 (by decide +kernel) (by decide +kernel)
theorem b397:B 40 5 e351:=viaPerm pc1_0 pci1_0 b391 (by decide +kernel) (by decide +kernel)
theorem b398:B 40 5 e352:=viaPerm pc1_0 pci1_0 b392 (by decide +kernel) (by decide +kernel)
theorem b399:B 40 5 e353:=viaSmall (by decide +kernel) (by decide)
theorem b400:B 40 5 e354:=viaSmall (by decide +kernel) (by decide)
theorem b401:B 40 5 e355:=viaSmall (by decide +kernel) (by decide)
theorem b402:B 40 5 e356:=viaSmall (by decide +kernel) (by decide)
theorem b403:B 40 5 e357:=viaSmall (by decide +kernel) (by decide)
theorem b404:B 40 5 e358:=viaSmall (by decide +kernel) (by decide)
theorem b405:B 40 5 e359:=viaSmall (by decide +kernel) (by decide)
theorem b406:B 40 5 e360:=viaSmall (by decide +kernel) (by decide)
theorem b407:B 40 5 e361:=viaSmall (by decide +kernel) (by decide)
theorem b408:B 40 5 e362:=viaSmall (by decide +kernel) (by decide)
theorem b409:B 40 5 e363:=viaSmall (by decide +kernel) (by decide)
theorem b410:B 40 5 e364:=viaSmall (by decide +kernel) (by decide)
theorem b411:B 40 5 e365:=viaPerm pc1_0 pci1_0 b405 (by decide +kernel) (by decide +kernel)
theorem b412:B 40 5 e366:=viaPerm pc1_0 pci1_0 b406 (by decide +kernel) (by decide +kernel)
theorem b413:B 40 5 e367:=viaPerm pc1_0 pci1_0 b407 (by decide +kernel) (by decide +kernel)
theorem b414:B 40 5 e368:=viaPerm pc1_0 pci1_0 b408 (by decide +kernel) (by decide +kernel)
theorem b415:B 40 5 e369:=viaPerm pc1_0 pci1_0 b409 (by decide +kernel) (by decide +kernel)
theorem b416:B 40 5 e370:=viaPerm pc1_0 pci1_0 b410 (by decide +kernel) (by decide +kernel)
theorem b417:B 40 5 e371:=viaSmall (by decide +kernel) (by decide)
theorem b418:B 40 5 e372:=viaSmall (by decide +kernel) (by decide)
theorem b419:B 40 5 e373:=viaSmall (by decide +kernel) (by decide)
theorem b420:B 40 5 e374:=viaSmall (by decide +kernel) (by decide)
theorem b421:B 40 5 e375:=viaPerm pc1_0 pci1_0 b417 (by decide +kernel) (by decide +kernel)
theorem b422:B 40 5 e376:=viaPerm pc1_0 pci1_0 b418 (by decide +kernel) (by decide +kernel)
theorem b423:B 40 5 e377:=viaPerm pc1_0 pci1_0 b419 (by decide +kernel) (by decide +kernel)
theorem b424:B 40 5 e378:=viaPerm pc1_0 pci1_0 b420 (by decide +kernel) (by decide +kernel)
theorem b425:B 40 5 e379:=viaSmall (by decide +kernel) (by decide)
theorem b426:B 40 5 e380:=viaSmall (by decide +kernel) (by decide)
theorem b427:B 40 5 e381:=viaSmall (by decide +kernel) (by decide)
theorem b428:B 40 5 e382:=viaPerm pc1_0 pci1_0 b427 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b429:B 40 6 e383:=viaBranch (ws:=[e332,e333,e334,e335,e336,e337,e338,e339,e340,e341,e342,e343,e344,e345,e346,e347,e348,e349,e350,e351,e352,e353,e354,e355,e356,e357,e358,e359,e360,e361,e362,e363,e364,e365,e366,e367,e368,e369,e370,e371,e372,e373,e374,e375,e376,e377,e378,e379,e380,e381,e382]) (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b426 (consBan b427 (consBan b428 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w430:W 40 6 e383:=widen (by decide +kernel) b429
theorem b431:B 89 7 e384:=viaCut pjt_1 w430 (by decide) (by decide +kernel) (by decide +kernel)
theorem b432:B 89 7 e385:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b433:B 6 2 e83:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b486:B 35 5 e435:=viaSmall (by decide +kernel) (by decide)
theorem b500:B 89 6 e330:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b501:B 89 6 e446:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b502:B 89 6 e447:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b503:B 89 6 e448:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b504:B 89 6 e449:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b505:B 89 6 e450:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b506:B 89 6 e451:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b507:B 89 6 e452:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b508:B 89 6 e453:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b509:B 89 6 e454:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b510:B 89 6 e455:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b511:B 89 6 e456:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b512:B 89 6 e457:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b513:B 89 6 e458:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b514:B 89 6 e459:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b515:B 89 6 e460:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b516:B 89 6 e461:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b517:B 89 6 e462:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b518:B 89 6 e463:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b519:B 89 6 e464:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b520:B 89 6 e465:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b521:B 89 6 e466:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b522:B 89 6 e467:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b523:B 89 6 e468:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b524:B 89 6 e469:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b525:B 89 6 e470:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b526:B 89 6 e471:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b527:B 89 6 e472:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem w528:W 20 4 e9:=widen (by decide +kernel) b16
theorem b529:B 89 6 e473:=viaCut pjt_11 w528 (by decide) (by decide +kernel) (by decide +kernel)
theorem b530:B 89 6 e474:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b531:B 89 6 e475:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b532:B 89 6 e476:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b533:B 89 6 e477:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b534:B 89 6 e478:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b535:B 89 6 e479:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b536:B 89 6 e480:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b537:B 89 6 e481:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b538:B 89 6 e482:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b539:B 89 6 e483:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b540:B 89 6 e484:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b541:B 89 6 e485:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b542:B 89 6 e486:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b543:B 89 6 e487:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b544:B 89 6 e488:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b545:B 89 6 e489:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b546:B 89 6 e490:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b547:B 89 6 e491:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b548:B 89 6 e492:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b549:B 89 6 e493:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b550:B 89 6 e494:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b551:B 89 6 e495:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b552:B 89 6 e496:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b553:B 89 6 e497:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b554:B 89 6 e498:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b555:B 89 6 e499:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b556:B 89 6 e500:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b557:B 89 6 e501:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b558:B 89 6 e502:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b559:B 89 6 e503:=viaCut pjt_11 w528 (by decide) (by decide +kernel) (by decide +kernel)
theorem b560:B 20 3 e9:=viaSmall (by decide +kernel) (by decide)
theorem w561:W 20 3 e9:=widen (by decide +kernel) b560
theorem b562:B 89 6 e504:=viaCut pjt_11 w561 (by decide) (by decide +kernel) (by decide +kernel)
theorem b563:B 89 6 e505:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b564:B 89 6 e506:=viaCut pjt_11 w561 (by decide) (by decide +kernel) (by decide +kernel)
theorem b565:B 89 6 e507:=viaCut pjt_11 w528 (by decide) (by decide +kernel) (by decide +kernel)
theorem b566:B 89 6 e508:=viaCut pjt_11 w561 (by decide) (by decide +kernel) (by decide +kernel)
theorem b567:B 89 6 e509:=viaCut pjt_11 w528 (by decide) (by decide +kernel) (by decide +kernel)
theorem b568:B 89 6 e510:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b569:B 89 6 e511:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b570:B 89 6 e512:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b571:B 89 6 e513:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b572:B 89 6 e514:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b573:B 89 6 e515:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b574:B 89 6 e516:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b575:B 89 6 e517:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b576:B 89 6 e518:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b577:B 89 6 e519:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b578:B 89 6 e520:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b579:B 89 6 e521:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b580:B 89 6 e522:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b581:B 89 6 e523:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b582:B 89 6 e524:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b583:B 89 6 e525:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b584:B 89 6 e526:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b585:B 89 6 e527:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b586:B 89 7 e76:=viaBranch (ws:=[e330,e75,e77,e446,e447,e448,e449,e450,e451,e452,e453,e454,e455,e456,e457,e458,e459,e460,e461,e462,e463,e464,e465,e466,e467,e468,e469,e470,e471,e472,e473,e474,e475,e476,e477,e478,e479,e480,e481,e482,e483,e484,e485,e486,e487,e488,e489,e490,e491,e492,e493,e494,e495,e496,e497,e498,e499,e500,e501,e502,e503,e504,e505,e506,e507,e508,e509,e510,e511,e512,e513,e514,e515,e516,e517,e518,e519,e520,e521,e522,e523,e524,e525,e526,e527]) (consBan b500 (consBan b91 (consBan b95 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b542 (consBan b543 (consBan b544 (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (consBan b553 (consBan b554 (consBan b555 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b587:B 89 7 e528:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b588:B 40 5 e383:=viaSmall (by decide +kernel) (by decide)
theorem b589:B 40 5 e529:=viaSmall (by decide +kernel) (by decide)
theorem b590:B 40 5 e530:=viaSmall (by decide +kernel) (by decide)
theorem b591:B 40 5 e531:=viaSmall (by decide +kernel) (by decide)
theorem b592:B 40 5 e532:=viaSmall (by decide +kernel) (by decide)
theorem b593:B 40 5 e533:=viaSmall (by decide +kernel) (by decide)
theorem b594:B 40 5 e534:=viaSmall (by decide +kernel) (by decide)
theorem b595:B 40 5 e535:=viaSmall (by decide +kernel) (by decide)
theorem b596:B 40 5 e536:=viaSmall (by decide +kernel) (by decide)
theorem b597:B 40 5 e537:=viaSmall (by decide +kernel) (by decide)
theorem b598:B 40 5 e538:=viaSmall (by decide +kernel) (by decide)
theorem b599:B 40 5 e539:=viaPerm pc1_0 pci1_0 b595 (by decide +kernel) (by decide +kernel)
theorem b600:B 40 5 e540:=viaPerm pc1_0 pci1_0 b596 (by decide +kernel) (by decide +kernel)
theorem b601:B 40 5 e541:=viaPerm pc1_0 pci1_0 b597 (by decide +kernel) (by decide +kernel)
theorem b602:B 40 5 e542:=viaPerm pc1_0 pci1_0 b598 (by decide +kernel) (by decide +kernel)
theorem b603:B 40 5 e543:=viaSmall (by decide +kernel) (by decide)
theorem b604:B 40 5 e544:=viaSmall (by decide +kernel) (by decide)
theorem b605:B 40 5 e545:=viaSmall (by decide +kernel) (by decide)
theorem b606:B 40 5 e546:=viaSmall (by decide +kernel) (by decide)
theorem b607:B 40 5 e547:=viaSmall (by decide +kernel) (by decide)
theorem b608:B 40 5 e548:=viaSmall (by decide +kernel) (by decide)
theorem b609:B 40 5 e549:=viaSmall (by decide +kernel) (by decide)
theorem b610:B 40 5 e550:=viaSmall (by decide +kernel) (by decide)
theorem b611:B 40 5 e551:=viaSmall (by decide +kernel) (by decide)
theorem b612:B 40 5 e552:=viaSmall (by decide +kernel) (by decide)
theorem b613:B 40 5 e553:=viaSmall (by decide +kernel) (by decide)
theorem b614:B 40 5 e554:=viaSmall (by decide +kernel) (by decide)
theorem b615:B 40 5 e555:=viaSmall (by decide +kernel) (by decide)
theorem b616:B 40 5 e556:=viaSmall (by decide +kernel) (by decide)
theorem b617:B 40 5 e557:=viaSmall (by decide +kernel) (by decide)
theorem b618:B 40 5 e558:=viaPerm pc1_0 pci1_0 b612 (by decide +kernel) (by decide +kernel)
theorem b619:B 40 5 e559:=viaPerm pc1_0 pci1_0 b613 (by decide +kernel) (by decide +kernel)
theorem b620:B 40 5 e560:=viaPerm pc1_0 pci1_0 b614 (by decide +kernel) (by decide +kernel)
theorem b621:B 40 5 e561:=viaPerm pc1_0 pci1_0 b615 (by decide +kernel) (by decide +kernel)
theorem b622:B 40 5 e562:=viaPerm pc1_0 pci1_0 b616 (by decide +kernel) (by decide +kernel)
theorem b623:B 40 5 e563:=viaPerm pc1_0 pci1_0 b617 (by decide +kernel) (by decide +kernel)
theorem b624:B 40 5 e564:=viaSmall (by decide +kernel) (by decide)
theorem b625:B 40 5 e565:=viaSmall (by decide +kernel) (by decide)
theorem b626:B 40 5 e566:=viaSmall (by decide +kernel) (by decide)
theorem b627:B 40 5 e567:=viaSmall (by decide +kernel) (by decide)
theorem b628:B 40 5 e568:=viaSmall (by decide +kernel) (by decide)
theorem b629:B 40 5 e569:=viaSmall (by decide +kernel) (by decide)
theorem b630:B 40 5 e570:=viaPerm pc1_0 pci1_0 b624 (by decide +kernel) (by decide +kernel)
theorem b631:B 40 5 e571:=viaPerm pc1_0 pci1_0 b625 (by decide +kernel) (by decide +kernel)
theorem b632:B 40 5 e572:=viaPerm pc1_0 pci1_0 b626 (by decide +kernel) (by decide +kernel)
theorem b633:B 40 5 e573:=viaPerm pc1_0 pci1_0 b627 (by decide +kernel) (by decide +kernel)
theorem b634:B 40 5 e574:=viaPerm pc1_0 pci1_0 b628 (by decide +kernel) (by decide +kernel)
theorem b635:B 40 5 e575:=viaPerm pc1_0 pci1_0 b629 (by decide +kernel) (by decide +kernel)
theorem b636:B 40 5 e576:=viaSmall (by decide +kernel) (by decide)
theorem b637:B 40 5 e577:=viaSmall (by decide +kernel) (by decide)
theorem b638:B 40 5 e578:=viaSmall (by decide +kernel) (by decide)
theorem b639:B 40 5 e579:=viaPerm pc1_0 pci1_0 b638 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b640:B 40 6 e339:=viaBranch (ws:=[e338,e383,e340,e529,e530,e531,e532,e533,e534,e535,e536,e537,e538,e539,e540,e541,e542,e543,e544,e545,e546,e547,e548,e549,e550,e551,e552,e553,e554,e555,e556,e557,e558,e559,e560,e561,e562,e563,e564,e565,e566,e567,e568,e569,e570,e571,e572,e573,e574,e575,e576,e577,e578,e579]) (consBan b384 (consBan b588 (consBan b386 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b595 (consBan b596 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (consBan b604 (consBan b605 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (consBan b639 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w641:W 40 6 e339:=widen (by decide +kernel) b640
theorem b642:B 89 7 e580:=viaCut pjt_1 w641 (by decide) (by decide +kernel) (by decide +kernel)
theorem b643:B 89 7 e581:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b644:B 89 7 e582:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b664:B 89 6 e602:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b665:B 89 6 e603:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b666:B 89 6 e604:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b667:B 89 6 e605:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b668:B 89 6 e606:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b669:B 89 6 e607:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b670:B 6 3 e608:=viaSmall (by decide +kernel) (by decide)
theorem w671:W 6 3 e608:=widen (by decide +kernel) b670
theorem b672:B 89 6 e609:=viaCut pjt_31 w671 (by decide) (by decide +kernel) (by decide +kernel)
theorem b673:B 89 6 e610:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b674:B 89 6 e611:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b675:B 89 6 e612:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b676:B 89 6 e613:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b677:B 89 6 e614:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b678:B 89 6 e615:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b679:B 89 6 e616:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b684:B 89 5 e620:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b685:B 89 5 e621:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b686:B 89 5 e622:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b687:B 89 5 e623:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b688:B 89 5 e624:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b689:B 89 5 e625:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b690:B 89 5 e626:=viaPerm pt0 pti0 b689 (by decide +kernel) (by decide +kernel)
theorem b691:B 89 5 e627:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b692:B 89 5 e628:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b693:B 89 5 e629:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b694:B 89 5 e630:=viaPerm pt0 pti0 b692 (by decide +kernel) (by decide +kernel)
theorem b695:B 89 5 e631:=viaPerm pt0 pti0 b693 (by decide +kernel) (by decide +kernel)
theorem b696:B 89 5 e632:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b697:B 89 5 e633:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b698:B 89 5 e634:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b699:B 89 5 e635:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b700:B 89 5 e636:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b701:B 89 5 e637:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b702:B 89 5 e638:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b703:B 89 5 e639:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b704:B 89 5 e640:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b705:B 89 5 e641:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b706:B 89 5 e642:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b707:B 89 5 e643:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b708:B 89 5 e644:=viaPerm pt0 pti0 b696 (by decide +kernel) (by decide +kernel)
theorem b709:B 89 5 e645:=viaPerm pt0 pti0 b697 (by decide +kernel) (by decide +kernel)
theorem b710:B 89 5 e646:=viaPerm pt0 pti0 b698 (by decide +kernel) (by decide +kernel)
theorem b711:B 89 5 e647:=viaPerm pt0 pti0 b700 (by decide +kernel) (by decide +kernel)
theorem b712:B 89 5 e648:=viaPerm pt0 pti0 b701 (by decide +kernel) (by decide +kernel)
theorem b713:B 89 5 e649:=viaPerm pt0 pti0 b699 (by decide +kernel) (by decide +kernel)
theorem b714:B 20 4 e650:=viaSmall (by decide +kernel) (by decide)
theorem w715:W 20 4 e650:=widen (by decide +kernel) b714
theorem b716:B 89 5 e651:=viaCut pjt_11 w715 (by decide) (by decide +kernel) (by decide +kernel)
theorem b717:B 89 5 e652:=viaCut pjt_11 w715 (by decide) (by decide +kernel) (by decide +kernel)
theorem b718:B 20 3 e650:=viaSmall (by decide +kernel) (by decide)
theorem w719:W 20 3 e650:=widen (by decide +kernel) b718
theorem b720:B 89 5 e653:=viaCut pjt_11 w719 (by decide) (by decide +kernel) (by decide +kernel)
theorem b721:B 89 5 e654:=viaPerm pt0 pti0 b720 (by decide +kernel) (by decide +kernel)
theorem b722:B 6 2 e655:=viaSmall (by decide +kernel) (by decide)
theorem w723:W 6 2 e655:=viaSub (ws:=[e83,e655]) (consBan b333 (consBan b722 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b724:B 89 5 e656:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b725:B 20 4 e650:=viaSmall (by decide +kernel) (by decide)
theorem b726:B 20 4 e657:=viaSmall (by decide +kernel) (by decide)
theorem w727:W 20 4 e657:=viaSub (ws:=[e650,e657]) (consBan b725 (consBan b726 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b728:B 89 5 e658:=viaCut pjt_15 w727 (by decide) (by decide +kernel) (by decide +kernel)
theorem b729:B 89 5 e659:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b730:B 89 5 e660:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b731:B 89 5 e661:=viaPerm pt0 pti0 b684 (by decide +kernel) (by decide +kernel)
theorem b732:B 89 5 e662:=viaPerm pt0 pti0 b685 (by decide +kernel) (by decide +kernel)
theorem b733:B 89 5 e663:=viaPerm pt0 pti0 b686 (by decide +kernel) (by decide +kernel)
theorem b734:B 89 5 e664:=viaPerm pt0 pti0 b687 (by decide +kernel) (by decide +kernel)
theorem b735:B 89 5 e665:=viaPerm pt0 pti0 b702 (by decide +kernel) (by decide +kernel)
theorem b736:B 89 5 e666:=viaPerm pt0 pti0 b703 (by decide +kernel) (by decide +kernel)
theorem b737:B 89 5 e667:=viaPerm pt0 pti0 b704 (by decide +kernel) (by decide +kernel)
theorem b738:B 89 5 e668:=viaPerm pt0 pti0 b705 (by decide +kernel) (by decide +kernel)
theorem b739:B 89 5 e669:=viaPerm pt0 pti0 b706 (by decide +kernel) (by decide +kernel)
theorem b740:B 89 5 e670:=viaPerm pt0 pti0 b707 (by decide +kernel) (by decide +kernel)
theorem b741:B 89 5 e671:=viaPerm pt0 pti0 b724 (by decide +kernel) (by decide +kernel)
theorem b742:B 89 5 e672:=viaPerm pt0 pti0 b728 (by decide +kernel) (by decide +kernel)
theorem b743:B 89 5 e673:=viaPerm pt0 pti0 b729 (by decide +kernel) (by decide +kernel)
theorem b744:B 89 5 e674:=viaPerm pt0 pti0 b730 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b745:B 89 6 e675:=viaBranch (ws:=[e620,e621,e622,e623,e624,e625,e626,e627,e628,e629,e630,e631,e632,e633,e634,e635,e636,e637,e638,e639,e640,e641,e642,e643,e644,e645,e646,e647,e648,e649,e651,e652,e653,e654,e656,e658,e659,e660,e661,e662,e663,e664,e665,e666,e667,e668,e669,e670,e671,e672,e673,e674]) (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b701 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b709 (consBan b710 (consBan b711 (consBan b712 (consBan b713 (consBan b716 (consBan b717 (consBan b720 (consBan b721 (consBan b724 (consBan b728 (consBan b729 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b738 (consBan b739 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w746:W 20 4 e650:=widen (by decide +kernel) b725
theorem b747:B 89 6 e676:=viaCut pjt_15 w746 (by decide) (by decide +kernel) (by decide +kernel)
theorem b748:B 89 6 e677:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b749:B 89 6 e678:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b750:B 89 6 e679:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b751:B 89 6 e680:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b752:B 89 6 e681:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b753:B 89 6 e682:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b754:B 89 6 e683:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b783:B 89 5 e712:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b784:B 89 5 e713:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b785:B 89 5 e714:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b786:B 89 5 e715:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b787:B 89 5 e716:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b788:B 89 5 e717:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b789:B 89 5 e718:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b790:B 89 5 e719:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b791:B 89 5 e720:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b792:B 89 5 e721:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b793:B 89 5 e722:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b794:B 89 5 e723:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b795:B 89 5 e724:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b796:B 89 5 e725:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b797:B 20 2 e726:=viaSmall (by decide +kernel) (by decide)
theorem w798:W 20 2 e726:=widen (by decide +kernel) b797
theorem b799:B 89 5 e727:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b800:B 89 5 e728:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b801:B 89 5 e729:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b802:B 89 5 e730:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b803:B 89 5 e731:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b804:B 89 5 e732:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b805:B 89 5 e733:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b806:B 89 5 e734:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b807:B 89 5 e735:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b808:B 89 5 e736:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b809:B 89 5 e737:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b810:B 89 5 e738:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b811:B 89 5 e739:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b812:B 89 5 e740:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b813:B 89 5 e741:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b814:B 20 3 e726:=viaSmall (by decide +kernel) (by decide)
theorem w815:W 20 3 e726:=widen (by decide +kernel) b814
theorem b816:B 89 5 e742:=viaCut pjt_15 w815 (by decide) (by decide +kernel) (by decide +kernel)
theorem b817:B 89 5 e743:=viaCut pjt_15 w815 (by decide) (by decide +kernel) (by decide +kernel)
theorem b818:B 89 5 e744:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b819:B 20 4 e745:=viaPerm pc11_0 pci11_0 b714 (by decide +kernel) (by decide +kernel)
theorem w820:W 20 4 e745:=widen (by decide +kernel) b819
theorem b821:B 89 5 e746:=viaCut pjt_11 w820 (by decide) (by decide +kernel) (by decide +kernel)
theorem b822:B 89 5 e747:=viaCut pjt_11 w820 (by decide) (by decide +kernel) (by decide +kernel)
theorem b823:B 20 3 e745:=viaPerm pc11_0 pci11_0 b718 (by decide +kernel) (by decide +kernel)
theorem w824:W 20 3 e745:=widen (by decide +kernel) b823
theorem b825:B 89 5 e748:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b826:B 89 5 e749:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b827:B 89 5 e750:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b828:B 89 5 e751:=viaCut pjt_15 w815 (by decide) (by decide +kernel) (by decide +kernel)
theorem b829:B 89 5 e752:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b830:B 89 5 e753:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b831:B 89 5 e754:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b832:B 89 5 e755:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b833:B 89 5 e756:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b834:B 89 5 e757:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b835:B 89 5 e758:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b836:B 89 5 e759:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b837:B 89 5 e760:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b838:B 89 5 e761:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b839:B 89 5 e762:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b840:B 89 5 e763:=viaCut pjt_15 w815 (by decide) (by decide +kernel) (by decide +kernel)
theorem b841:B 89 5 e764:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b842:B 89 5 e765:=viaCut pjt_15 w815 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b843:B 89 6 e766:=viaBranch (ws:=[e712,e713,e714,e715,e716,e717,e718,e719,e720,e721,e722,e723,e724,e725,e727,e728,e729,e730,e731,e732,e733,e734,e735,e736,e737,e738,e739,e740,e741,e742,e743,e744,e746,e747,e748,e749,e750,e751,e752,e753,e754,e755,e756,e757,e758,e759,e760,e761,e762,e763,e764,e765]) (consBan b783 (consBan b784 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b792 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b808 (consBan b809 (consBan b810 (consBan b811 (consBan b812 (consBan b813 (consBan b816 (consBan b817 (consBan b818 (consBan b821 (consBan b822 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (consBan b829 (consBan b830 (consBan b831 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b850:B 89 5 e770:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b851:B 89 5 e771:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b852:B 89 5 e772:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b853:B 89 5 e773:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b854:B 89 5 e774:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b855:B 89 5 e775:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b856:B 89 5 e776:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b857:B 89 5 e777:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b858:B 89 5 e778:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b859:B 89 5 e779:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b860:B 89 5 e780:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b861:B 89 5 e781:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b862:B 89 5 e782:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b863:B 89 5 e783:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b864:B 89 5 e784:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b865:B 89 5 e785:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b866:B 89 5 e786:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b867:B 89 5 e787:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b868:B 20 4 e126:=viaSmall (by decide +kernel) (by decide)
theorem w869:W 20 4 e126:=widen (by decide +kernel) b868
theorem b870:B 89 5 e788:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b871:B 6 2 e608:=viaSmall (by decide +kernel) (by decide)
theorem w872:W 6 2 e608:=widen (by decide +kernel) b871
theorem b873:B 89 5 e789:=viaCut pjt_31 w872 (by decide) (by decide +kernel) (by decide +kernel)
theorem w874:W 16 3 e124:=widen (by decide +kernel) b145
theorem b875:B 89 5 e790:=viaCut pjt_16 w874 (by decide) (by decide +kernel) (by decide +kernel)
theorem b876:B 89 5 e791:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b877:B 89 5 e792:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b878:B 89 5 e793:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b879:B 89 5 e794:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b880:B 89 5 e795:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b881:B 89 5 e796:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b882:B 89 5 e797:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b883:B 89 5 e798:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b884:B 89 5 e799:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b885:B 89 5 e800:=viaCut pjt_15 w798 (by decide) (by decide +kernel) (by decide +kernel)
theorem b886:B 89 5 e801:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b887:B 89 5 e802:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b888:B 89 5 e803:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b889:B 89 5 e804:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b890:B 89 5 e805:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b891:B 89 6 e806:=viaBranch (ws:=[e770,e771,e772,e773,e774,e775,e776,e777,e778,e779,e780,e781,e782,e783,e784,e785,e786,e747,e787,e749,e788,e789,e790,e791,e792,e793,e794,e795,e796,e797,e798,e799,e800,e801,e802,e803,e804,e805]) (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (consBan b855 (consBan b856 (consBan b857 (consBan b858 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b864 (consBan b865 (consBan b866 (consBan b822 (consBan b867 (consBan b826 (consBan b870 (consBan b873 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (consBan b889 (consBan b890 (nilBan _ _))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b892:B 89 6 e807:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b893:B 89 6 e808:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b894:B 89 6 e805:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b895:B 89 6 e809:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b896:B 89 6 e810:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b897:B 89 6 e811:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b898:B 89 6 e812:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b899:B 89 6 e813:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b900:B 89 6 e814:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b901:B 89 6 e815:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b902:B 89 6 e816:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b903:B 89 6 e817:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b904:B 89 6 e818:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b905:B 89 6 e819:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b906:B 89 6 e820:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b907:B 89 6 e821:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b908:B 89 6 e822:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b909:B 89 6 e823:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b910:B 89 6 e824:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b911:B 89 6 e825:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b912:B 89 6 e826:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b913:B 89 6 e827:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b914:B 89 6 e828:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b915:B 89 6 e829:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b916:B 89 6 e830:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b917:B 89 6 e831:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b918:B 89 6 e832:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b919:B 89 6 e833:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b920:B 89 6 e834:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b921:B 89 6 e835:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b922:B 89 6 e836:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b923:B 89 6 e837:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b924:B 89 6 e838:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b925:B 89 6 e839:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b926:B 89 6 e840:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b927:B 89 6 e841:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b928:B 89 6 e842:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b929:B 89 6 e843:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b930:B 20 3 e650:=viaSmall (by decide +kernel) (by decide)
theorem w931:W 20 3 e650:=widen (by decide +kernel) b930
theorem b932:B 89 6 e844:=viaCut pjt_15 w931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b933:B 89 6 e845:=viaCut pjt_15 w746 (by decide) (by decide +kernel) (by decide +kernel)
theorem b934:B 89 6 e846:=viaCut pjt_15 w746 (by decide) (by decide +kernel) (by decide +kernel)
theorem b935:B 89 6 e847:=viaCut pjt_15 w931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b936:B 89 6 e848:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b937:B 89 6 e849:=viaCut pjt_15 w727 (by decide) (by decide +kernel) (by decide +kernel)
theorem b938:B 89 6 e850:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b939:B 89 6 e851:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b940:B 89 6 e852:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b941:B 16 4 e124:=viaSmall (by decide +kernel) (by decide)
theorem w942:W 16 4 e124:=widen (by decide +kernel) b941
theorem b943:B 89 6 e853:=viaCut pjt_16 w942 (by decide) (by decide +kernel) (by decide +kernel)
theorem b944:B 89 6 e854:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b945:B 89 6 e855:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b946:B 89 6 e856:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b947:B 89 6 e857:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b948:B 89 6 e858:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b949:B 89 6 e859:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b950:B 89 6 e860:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b951:B 89 6 e861:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b952:B 89 6 e862:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b953:B 89 6 e863:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b954:B 89 6 e864:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b955:B 89 6 e865:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b956:B 89 6 e866:=viaCut pjt_15 w931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b957:B 89 6 e867:=viaCut pjt_15 w746 (by decide) (by decide +kernel) (by decide +kernel)
theorem b958:B 89 6 e868:=viaCut pjt_15 w931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b959:B 89 6 e869:=viaCut pjt_15 w746 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b960:B 89 7 e870:=viaBranch (ws:=[e602,e603,e604,e605,e606,e607,e609,e610,e611,e612,e613,e614,e615,e616,e675,e676,e677,e678,e679,e680,e681,e682,e683,e766,e806,e807,e808,e805,e809,e810,e811,e812,e813,e814,e815,e816,e817,e818,e819,e820,e821,e822,e823,e824,e825,e826,e827,e828,e829,e830,e831,e832,e833,e834,e835,e836,e837,e838,e839,e840,e841,e842,e843,e844,e845,e846,e847,e848,e849,e850,e851,e852,e853,e854,e855,e856,e857,e858,e859,e860,e861,e862,e863,e864,e865,e866,e867,e868,e869]) (consBan b664 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (consBan b672 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b745 (consBan b747 (consBan b748 (consBan b749 (consBan b750 (consBan b751 (consBan b752 (consBan b753 (consBan b754 (consBan b843 (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (consBan b902 (consBan b903 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b908 (consBan b909 (consBan b910 (consBan b911 (consBan b912 (consBan b913 (consBan b914 (consBan b915 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b920 (consBan b921 (consBan b922 (consBan b923 (consBan b924 (consBan b925 (consBan b926 (consBan b927 (consBan b928 (consBan b929 (consBan b932 (consBan b933 (consBan b934 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b940 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (consBan b947 (consBan b948 (consBan b949 (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b959 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b966:B 89 6 e873:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b967:B 89 6 e874:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b968:B 89 6 e875:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b969:B 89 6 e876:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b970:B 89 6 e877:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b971:B 89 6 e878:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b972:B 89 6 e879:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b973:B 20 3 e126:=viaSmall (by decide +kernel) (by decide)
theorem w974:W 20 3 e126:=widen (by decide +kernel) b973
theorem b975:B 89 6 e880:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b976:B 89 6 e881:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b978:B 40 5 e883:=viaSmall (by decide +kernel) (by decide)
theorem w979:W 40 5 e883:=widen (by decide +kernel) b978
theorem b980:B 89 6 e884:=viaCut pjt_2 w979 (by decide) (by decide +kernel) (by decide +kernel)
theorem b981:B 89 6 e885:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b982:B 89 6 e886:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b983:B 89 6 e887:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b984:B 89 6 e888:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b985:B 89 6 e889:=viaPerm pt0 pti0 b747 (by decide +kernel) (by decide +kernel)
theorem b986:B 20 4 e890:=viaSmall (by decide +kernel) (by decide)
theorem w987:W 20 4 e890:=viaSub (ws:=[e126,e650,e890]) (consBan b147 (consBan b725 (consBan b986 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b988:B 89 6 e891:=viaCut pjt_15 w987 (by decide) (by decide +kernel) (by decide +kernel)
theorem b989:B 89 6 e892:=viaPerm pt0 pti0 b749 (by decide +kernel) (by decide +kernel)
theorem b990:B 89 6 e893:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b991:B 89 6 e894:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b992:B 89 6 e895:=viaCut pjt_11 w820 (by decide) (by decide +kernel) (by decide +kernel)
theorem b993:B 20 4 e896:=viaSmall (by decide +kernel) (by decide)
theorem w994:W 20 4 e896:=viaSub (ws:=[e126,e745,e896]) (consBan b868 (consBan b819 (consBan b993 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b995:B 89 6 e897:=viaCut pjt_11 w994 (by decide) (by decide +kernel) (by decide +kernel)
theorem b996:B 89 6 e898:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b997:B 89 6 e899:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b998:B 89 6 e900:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b999:B 89 6 e901:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1000:B 89 6 e902:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1001:B 89 6 e903:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1002:B 89 6 e904:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1003:B 89 6 e905:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1004:B 89 6 e906:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1005:B 89 6 e907:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1006:B 89 6 e908:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1007:B 35 5 e909:=viaSmall (by decide +kernel) (by decide)
theorem w1008:W 35 5 e909:=widen (by decide +kernel) b1007
theorem b1009:B 89 6 e910:=viaCut pjt_0 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1010:B 89 6 e911:=viaCut pjt_0 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1011:B 89 6 e912:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1012:B 89 6 e913:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1013:B 89 6 e914:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1014:B 89 6 e915:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1015:B 89 6 e916:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1016:B 89 6 e917:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1017:B 89 6 e918:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1018:B 89 6 e919:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1019:B 89 6 e920:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1020:B 89 6 e921:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1021:B 89 6 e922:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1022:B 89 6 e923:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1023:B 89 6 e924:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1024:B 89 6 e925:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1025:B 89 6 e926:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1026:B 89 6 e927:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1027:B 89 6 e928:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1028:B 89 6 e929:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1029:B 89 6 e930:=viaCut pjt_15 w931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1030:B 89 6 e931:=viaCut pjt_15 w987 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1031:B 89 6 e932:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1032:B 89 6 e933:=viaCut pjt_15 w931 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1033:B 89 6 e934:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1034:B 20 4 e126:=viaSmall (by decide +kernel) (by decide)
theorem b1035:B 20 4 e935:=viaSmall (by decide +kernel) (by decide)
theorem b1036:B 20 4 e936:=viaSmall (by decide +kernel) (by decide)
theorem w1037:W 20 4 e936:=viaSub (ws:=[e126,e935,e936]) (consBan b1034 (consBan b1035 (consBan b1036 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1038:B 89 6 e937:=viaCut pjt_6 w1037 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1039:B 89 6 e938:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1040:B 89 6 e939:=viaCut pjt_31 w723 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1041:B 89 6 e940:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1042:B 89 6 e941:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1043:B 89 6 e942:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1044:B 89 6 e943:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1045:B 89 6 e944:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1047:B 89 6 e945:=viaCut pjt_15 w987 (by decide) (by decide +kernel) (by decide +kernel)
theorem w1048:W 12 3 e0:=viaSub (ws:=[e16,e0]) (consBan b30 (consBan b0 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1049:B 89 6 e946:=viaCut pjt_18 w1048 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1050:B 89 6 e947:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1051:B 6 2 e83:=viaSmall (by decide +kernel) (by decide)
theorem b1052:B 89 6 e948:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1054:B 20 4 e949:=viaSmall (by decide +kernel) (by decide)
theorem w1055:W 20 4 e949:=viaSub (ws:=[e126,e949]) (consBan b147 (consBan b1054 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1056:B 89 6 e950:=viaCut pjt_15 w1055 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1057:B 89 6 e951:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1058:B 89 6 e952:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1059:B 16 3 e953:=viaPerm pc8_0 pci8_0 b204 (by decide +kernel) (by decide +kernel)
theorem w1060:W 16 3 e953:=widen (by decide +kernel) b1059
theorem b1061:B 89 6 e954:=viaCut pjt_8 w1060 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1062:B 89 6 e955:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1063:B 89 6 e956:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1064:B 89 6 e957:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1065:B 89 6 e958:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1066:B 89 6 e959:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1067:B 89 7 e960:=viaBranch (ws:=[e873,e874,e875,e876,e877,e878,e879,e609,e880,e611,e881,e884,e885,e886,e887,e888,e889,e891,e892,e893,e894,e895,e897,e898,e899,e900,e901,e902,e903,e904,e905,e906,e907,e908,e910,e911,e912,e913,e914,e915,e916,e917,e918,e919,e920,e921,e922,e923,e924,e925,e926,e927,e928,e929,e930,e931,e932,e933,e934,e937,e938,e939,e940,e941,e942,e943,e944,e945,e946,e947,e948,e950,e951,e952,e954,e955,e956,e957,e958,e959]) (consBan b966 (consBan b967 (consBan b968 (consBan b969 (consBan b970 (consBan b971 (consBan b972 (consBan b672 (consBan b975 (consBan b674 (consBan b976 (consBan b980 (consBan b981 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b988 (consBan b989 (consBan b990 (consBan b991 (consBan b992 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1006 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1012 (consBan b1013 (consBan b1014 (consBan b1015 (consBan b1016 (consBan b1017 (consBan b1018 (consBan b1019 (consBan b1020 (consBan b1021 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b1025 (consBan b1026 (consBan b1027 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (consBan b1038 (consBan b1039 (consBan b1040 (consBan b1041 (consBan b1042 (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1047 (consBan b1049 (consBan b1050 (consBan b1052 (consBan b1056 (consBan b1057 (consBan b1058 (consBan b1061 (consBan b1062 (consBan b1063 (consBan b1064 (consBan b1065 (consBan b1066 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1068:B 89 7 e925:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1086:B 89 6 e977:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1087:B 89 6 e978:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1088:B 89 6 e979:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1089:B 89 6 e980:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1090:B 89 6 e981:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1091:B 89 6 e870:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1092:B 89 6 e982:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1093:B 89 6 e983:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1094:B 89 6 e984:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1095:B 89 6 e985:=viaPerm pt0 pti0 b519 (by decide +kernel) (by decide +kernel)
theorem b1096:B 89 6 e986:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1097:B 89 6 e987:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1098:B 89 6 e988:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1099:B 89 6 e989:=viaPerm pt0 pti0 b752 (by decide +kernel) (by decide +kernel)
theorem b1100:B 89 6 e990:=viaPerm pt0 pti0 b991 (by decide +kernel) (by decide +kernel)
theorem b1101:B 89 6 e991:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1102:B 89 6 e992:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1103:B 89 6 e993:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1104:B 89 6 e994:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1105:B 89 6 e995:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1106:B 89 6 e996:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1107:B 89 6 e997:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1108:B 89 6 e998:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1109:B 89 6 e999:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1110:B 89 6 e1000:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1111:B 89 6 e1001:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1112:B 89 6 e1002:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1113:B 89 6 e1003:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1114:B 89 6 e1004:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1115:B 89 6 e1005:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1116:B 89 6 e1006:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1117:B 89 6 e1007:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1118:B 89 6 e1008:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1119:B 89 6 e1009:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1120:B 89 6 e1010:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1121:B 89 6 e1011:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1122:B 89 6 e1012:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1123:B 89 6 e1013:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1124:B 89 6 e1014:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1125:B 89 6 e1015:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1126:B 89 6 e1016:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1127:B 89 6 e1017:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1128:B 89 6 e1018:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1129:B 89 6 e1019:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1130:B 89 6 e1020:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1131:B 89 6 e1021:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1132:B 89 6 e1022:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1133:B 89 6 e1023:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1134:B 89 6 e1024:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1135:B 89 6 e1025:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1136:B 89 6 e1026:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1137:B 89 6 e1027:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1138:B 89 6 e1028:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1139:B 89 6 e1029:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1140:B 89 6 e1030:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1141:B 89 6 e1031:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1142:B 89 6 e1032:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1143:B 89 6 e1033:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem w1144:W 20 3 e12:=widen (by decide +kernel) b26
theorem b1145:B 89 6 e1034:=viaCut pjt_15 w1144 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1146:B 20 4 e12:=viaSmall (by decide +kernel) (by decide)
theorem w1147:W 20 4 e12:=widen (by decide +kernel) b1146
theorem b1148:B 89 6 e1035:=viaCut pjt_15 w1147 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1149:B 89 6 e1036:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1150:B 89 6 e1037:=viaCut pjt_15 w1144 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1151:B 89 6 e1038:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1152:B 89 6 e1039:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1153:B 89 6 e1040:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1154:B 89 6 e1041:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1155:B 89 6 e1042:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1164:B 89 6 e1051:=viaCut pjt_15 w1147 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1165:B 89 6 e1052:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1166:B 89 6 e1053:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1167:B 89 6 e1054:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1168:B 89 6 e1055:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1169:B 89 6 e1056:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1170:B 89 6 e1057:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1171:B 89 6 e1058:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1172:B 89 6 e1059:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1173:B 89 6 e1060:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1174:B 89 6 e1061:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1175:B 89 6 e1062:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1176:B 89 6 e1063:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1177:B 89 6 e1064:=viaCut pjt_15 w1144 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1178:B 89 6 e1065:=viaCut pjt_15 w1147 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1179:B 89 6 e1066:=viaCut pjt_15 w1144 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1180:B 89 6 e1067:=viaCut pjt_15 w1147 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1181:B 89 7 e610:=viaBranch (ws:=[e977,e978,e979,e450,e980,e981,e609,e870,e611,e982,e983,e984,e985,e986,e987,e988,e989,e990,e991,e992,e993,e994,e995,e996,e997,e998,e999,e1000,e1001,e1002,e1003,e1004,e1005,e1006,e1007,e1008,e1009,e1010,e1011,e1012,e1013,e1014,e1015,e1016,e1017,e1018,e1019,e1020,e1021,e1022,e1023,e1024,e1025,e1026,e1027,e1028,e1029,e1030,e1031,e1032,e1033,e1034,e1035,e1036,e1037,e1038,e1039,e1040,e1041,e1042,e1051,e1052,e1053,e1054,e1055,e1056,e1057,e1058,e1059,e1060,e1061,e1062,e1063,e1064,e1065,e1066,e1067]) (consBan b1086 (consBan b1087 (consBan b1088 (consBan b505 (consBan b1089 (consBan b1090 (consBan b672 (consBan b1091 (consBan b674 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (consBan b1097 (consBan b1098 (consBan b1099 (consBan b1100 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (consBan b1107 (consBan b1108 (consBan b1109 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1114 (consBan b1115 (consBan b1116 (consBan b1117 (consBan b1118 (consBan b1119 (consBan b1120 (consBan b1121 (consBan b1122 (consBan b1123 (consBan b1124 (consBan b1125 (consBan b1126 (consBan b1127 (consBan b1128 (consBan b1129 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1134 (consBan b1135 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1140 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1145 (consBan b1148 (consBan b1149 (consBan b1150 (consBan b1151 (consBan b1152 (consBan b1153 (consBan b1154 (consBan b1155 (consBan b1164 (consBan b1165 (consBan b1166 (consBan b1167 (consBan b1168 (consBan b1169 (consBan b1170 (consBan b1171 (consBan b1172 (consBan b1173 (consBan b1174 (consBan b1175 (consBan b1176 (consBan b1177 (consBan b1178 (consBan b1179 (consBan b1180 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1182:B 89 7 e881:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1183:B 89 7 e1068:=viaPerm pt0 pti0 b32 (by decide +kernel) (by decide +kernel)
theorem b1184:B 89 7 e1069:=viaPerm pt0 pti0 b375 (by decide +kernel) (by decide +kernel)
theorem b1185:B 89 7 e1070:=viaPerm pt0 pti0 b431 (by decide +kernel) (by decide +kernel)
theorem b1186:B 89 7 e1071:=viaPerm pt0 pti0 b432 (by decide +kernel) (by decide +kernel)
theorem b1187:B 89 7 e1072:=viaPerm pt0 pti0 b586 (by decide +kernel) (by decide +kernel)
theorem b1188:B 89 7 e1073:=viaPerm pt0 pti0 b587 (by decide +kernel) (by decide +kernel)
theorem b1189:B 89 7 e1074:=viaPerm pt0 pti0 b642 (by decide +kernel) (by decide +kernel)
theorem b1190:B 89 7 e1075:=viaPerm pt0 pti0 b643 (by decide +kernel) (by decide +kernel)
theorem b1191:B 89 7 e1076:=viaPerm pt0 pti0 b644 (by decide +kernel) (by decide +kernel)
theorem b1192:B 89 7 e1077:=viaPerm pt0 pti0 b960 (by decide +kernel) (by decide +kernel)
theorem b1193:B 89 7 e1078:=viaPerm pt0 pti0 b1067 (by decide +kernel) (by decide +kernel)
theorem b1194:B 89 7 e1079:=viaPerm pt0 pti0 b1068 (by decide +kernel) (by decide +kernel)
theorem b1195:B 89 7 e1080:=viaPerm pt0 pti0 b1181 (by decide +kernel) (by decide +kernel)
theorem b1196:B 89 7 e1081:=viaPerm pt0 pti0 b1182 (by decide +kernel) (by decide +kernel)
theorem b1197:B 89 7 e1082:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1202:B 89 6 e1086:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1203:B 89 6 e1087:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1204:B 89 6 e1088:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1205:B 89 6 e1089:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1206:B 89 6 e1090:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1207:B 89 6 e1091:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1208:B 89 6 e1092:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1209:B 89 6 e1093:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1210:B 89 6 e1094:=viaPerm pt0 pti0 b1202 (by decide +kernel) (by decide +kernel)
theorem b1211:B 89 6 e1095:=viaPerm pt0 pti0 b1203 (by decide +kernel) (by decide +kernel)
theorem b1212:B 89 6 e1096:=viaPerm pt0 pti0 b1204 (by decide +kernel) (by decide +kernel)
theorem b1213:B 89 6 e1097:=viaPerm pt0 pti0 b1205 (by decide +kernel) (by decide +kernel)
theorem b1214:B 89 6 e1098:=viaPerm pt0 pti0 b1206 (by decide +kernel) (by decide +kernel)
theorem b1215:B 89 6 e1099:=viaPerm pt0 pti0 b843 (by decide +kernel) (by decide +kernel)
theorem b1216:B 89 6 e1100:=viaPerm pt0 pti0 b992 (by decide +kernel) (by decide +kernel)
theorem b1217:B 89 6 e1101:=viaPerm pt0 pti0 b892 (by decide +kernel) (by decide +kernel)
theorem b1218:B 89 6 e1102:=viaPerm pt0 pti0 b996 (by decide +kernel) (by decide +kernel)
theorem b1219:B 89 6 e1103:=viaPerm pt0 pti0 b1207 (by decide +kernel) (by decide +kernel)
theorem b1220:B 89 6 e1104:=viaPerm pt0 pti0 b1208 (by decide +kernel) (by decide +kernel)
theorem b1221:B 89 6 e1105:=viaPerm pt0 pti0 b1105 (by decide +kernel) (by decide +kernel)
theorem b1222:B 89 6 e1106:=viaPerm pt0 pti0 b1209 (by decide +kernel) (by decide +kernel)
theorem b1223:B 6 3 e608:=viaSmall (by decide +kernel) (by decide)
theorem w1224:W 6 3 e608:=widen (by decide +kernel) b1223
theorem b1225:B 89 6 e1107:=viaCut pjt_26 w1224 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1226:B 89 6 e1108:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1227:B 89 6 e1109:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1228:B 89 6 e1110:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1229:B 16 4 e1111:=viaSmall (by decide +kernel) (by decide)
theorem w1230:W 16 4 e1111:=widen (by decide +kernel) b1229
theorem b1231:B 89 6 e1112:=viaCut pjt_12 w1230 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1232:B 89 6 e1113:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1233:B 89 6 e1114:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1234:B 89 6 e1115:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1235:B 89 6 e1116:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1236:B 89 6 e1117:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1237:B 89 6 e1118:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1238:B 89 6 e1119:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1239:B 89 6 e1120:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1240:B 89 6 e1121:=viaPerm pt0 pti0 b1239 (by decide +kernel) (by decide +kernel)
theorem b1241:B 89 6 e1122:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1242:B 89 6 e1123:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1243:B 89 6 e1124:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1244:B 89 6 e1125:=viaPerm pt0 pti0 b1242 (by decide +kernel) (by decide +kernel)
theorem b1245:B 89 6 e1126:=viaPerm pt0 pti0 b1243 (by decide +kernel) (by decide +kernel)
theorem b1246:B 89 6 e1127:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1247:B 89 6 e1128:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1248:B 89 6 e1129:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1249:B 89 6 e1130:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1250:B 89 6 e1131:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1251:B 89 6 e1132:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1252:B 89 6 e1133:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1253:B 89 6 e1134:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1254:B 89 6 e1135:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1255:B 89 6 e1136:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1256:B 89 6 e1137:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1257:B 89 6 e1138:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1258:B 89 6 e1139:=viaPerm pt0 pti0 b1246 (by decide +kernel) (by decide +kernel)
theorem b1259:B 89 6 e1140:=viaPerm pt0 pti0 b1247 (by decide +kernel) (by decide +kernel)
theorem b1260:B 89 6 e1141:=viaPerm pt0 pti0 b1248 (by decide +kernel) (by decide +kernel)
theorem b1261:B 89 6 e1142:=viaPerm pt0 pti0 b1250 (by decide +kernel) (by decide +kernel)
theorem b1262:B 89 6 e1143:=viaPerm pt0 pti0 b1251 (by decide +kernel) (by decide +kernel)
theorem b1263:B 89 6 e1144:=viaPerm pt0 pti0 b1249 (by decide +kernel) (by decide +kernel)
theorem b1264:B 89 6 e1145:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1265:B 89 6 e1146:=viaCut pjt_11 w820 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1266:B 89 6 e1147:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1267:B 89 6 e1148:=viaPerm pt0 pti0 b1266 (by decide +kernel) (by decide +kernel)
theorem b1268:B 89 6 e1149:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1269:B 89 6 e1150:=viaCut pjt_11 w820 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1270:B 89 6 e1151:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1271:B 89 6 e1152:=viaCut pjt_11 w820 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1272:B 89 6 e1153:=viaPerm pt0 pti0 b1228 (by decide +kernel) (by decide +kernel)
theorem b1273:B 89 6 e1154:=viaPerm pt0 pti0 b1231 (by decide +kernel) (by decide +kernel)
theorem b1274:B 89 6 e1155:=viaPerm pt0 pti0 b1232 (by decide +kernel) (by decide +kernel)
theorem b1275:B 89 6 e1156:=viaPerm pt0 pti0 b1233 (by decide +kernel) (by decide +kernel)
theorem b1276:B 89 6 e1157:=viaPerm pt0 pti0 b1234 (by decide +kernel) (by decide +kernel)
theorem b1277:B 89 6 e1158:=viaPerm pt0 pti0 b1235 (by decide +kernel) (by decide +kernel)
theorem b1278:B 89 6 e1159:=viaPerm pt0 pti0 b1236 (by decide +kernel) (by decide +kernel)
theorem b1279:B 89 6 e1160:=viaPerm pt0 pti0 b1237 (by decide +kernel) (by decide +kernel)
theorem b1280:B 89 6 e1161:=viaPerm pt0 pti0 b1252 (by decide +kernel) (by decide +kernel)
theorem b1281:B 89 6 e1162:=viaPerm pt0 pti0 b1253 (by decide +kernel) (by decide +kernel)
theorem b1282:B 89 6 e1163:=viaPerm pt0 pti0 b1254 (by decide +kernel) (by decide +kernel)
theorem b1283:B 89 6 e1164:=viaPerm pt0 pti0 b1255 (by decide +kernel) (by decide +kernel)
theorem b1284:B 89 6 e1165:=viaPerm pt0 pti0 b1256 (by decide +kernel) (by decide +kernel)
theorem b1285:B 89 6 e1166:=viaPerm pt0 pti0 b1257 (by decide +kernel) (by decide +kernel)
theorem b1286:B 89 6 e1167:=viaPerm pt0 pti0 b1268 (by decide +kernel) (by decide +kernel)
theorem b1287:B 89 6 e1168:=viaPerm pt0 pti0 b1269 (by decide +kernel) (by decide +kernel)
theorem b1288:B 89 6 e1169:=viaPerm pt0 pti0 b1270 (by decide +kernel) (by decide +kernel)
theorem b1289:B 89 6 e1170:=viaPerm pt0 pti0 b1271 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1290:B 89 7 e1171:=viaBranch (ws:=[e1086,e1087,e1088,e1089,e1090,e766,e895,e807,e898,e1091,e1092,e995,e1093,e1094,e1095,e1096,e1097,e1098,e1099,e1100,e1101,e1102,e1103,e1104,e1105,e1106,e1107,e1108,e1109,e1110,e1112,e1113,e1114,e1115,e1116,e1117,e1118,e1119,e1120,e1121,e1122,e1123,e1124,e1125,e1126,e1127,e1128,e1129,e1130,e1131,e1132,e1133,e1134,e1135,e1136,e1137,e1138,e1139,e1140,e1141,e1142,e1143,e1144,e1145,e1146,e1147,e1148,e1149,e1150,e1151,e1152,e1153,e1154,e1155,e1156,e1157,e1158,e1159,e1160,e1161,e1162,e1163,e1164,e1165,e1166,e1167,e1168,e1169,e1170]) (consBan b1202 (consBan b1203 (consBan b1204 (consBan b1205 (consBan b1206 (consBan b843 (consBan b992 (consBan b892 (consBan b996 (consBan b1207 (consBan b1208 (consBan b1105 (consBan b1209 (consBan b1210 (consBan b1211 (consBan b1212 (consBan b1213 (consBan b1214 (consBan b1215 (consBan b1216 (consBan b1217 (consBan b1218 (consBan b1219 (consBan b1220 (consBan b1221 (consBan b1222 (consBan b1225 (consBan b1226 (consBan b1227 (consBan b1228 (consBan b1231 (consBan b1232 (consBan b1233 (consBan b1234 (consBan b1235 (consBan b1236 (consBan b1237 (consBan b1238 (consBan b1239 (consBan b1240 (consBan b1241 (consBan b1242 (consBan b1243 (consBan b1244 (consBan b1245 (consBan b1246 (consBan b1247 (consBan b1248 (consBan b1249 (consBan b1250 (consBan b1251 (consBan b1252 (consBan b1253 (consBan b1254 (consBan b1255 (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1259 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b1263 (consBan b1264 (consBan b1265 (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1270 (consBan b1271 (consBan b1272 (consBan b1273 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b1277 (consBan b1278 (consBan b1279 (consBan b1280 (consBan b1281 (consBan b1282 (consBan b1283 (consBan b1284 (consBan b1285 (consBan b1286 (consBan b1287 (consBan b1288 (consBan b1289 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w1291:W 40 5 e348:=widen (by decide +kernel) b394
theorem b1292:B 89 6 e1172:=viaCut pjt_1 w1291 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1293:B 89 6 e1173:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1294:B 89 6 e1174:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1295:B 89 6 e1175:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1296:B 89 6 e1176:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1297:B 89 6 e1177:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1298:B 89 6 e1178:=viaPerm pt0 pti0 b1292 (by decide +kernel) (by decide +kernel)
theorem b1299:B 89 6 e1179:=viaPerm pt0 pti0 b1293 (by decide +kernel) (by decide +kernel)
theorem b1300:B 89 6 e1180:=viaPerm pt0 pti0 b1294 (by decide +kernel) (by decide +kernel)
theorem b1301:B 89 6 e1181:=viaPerm pt0 pti0 b1295 (by decide +kernel) (by decide +kernel)
theorem b1302:B 89 6 e1182:=viaPerm pt0 pti0 b1296 (by decide +kernel) (by decide +kernel)
theorem b1303:B 89 6 e1183:=viaPerm pt0 pti0 b891 (by decide +kernel) (by decide +kernel)
theorem b1304:B 89 6 e1184:=viaPerm pt0 pti0 b995 (by decide +kernel) (by decide +kernel)
theorem b1305:B 89 6 e1185:=viaPerm pt0 pti0 b893 (by decide +kernel) (by decide +kernel)
theorem b1306:B 89 6 e1186:=viaPerm pt0 pti0 b1297 (by decide +kernel) (by decide +kernel)
theorem b1307:B 89 6 e1187:=viaPerm pt0 pti0 b1106 (by decide +kernel) (by decide +kernel)
theorem b1308:B 89 6 e1188:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1309:B 89 6 e1189:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1310:B 89 6 e1190:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1311:B 89 6 e1191:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1312:B 89 6 e1192:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1313:B 89 6 e1193:=viaCut pjt_0 w1008 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1314:B 89 6 e1194:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1315:B 89 6 e1195:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1316:B 89 6 e1196:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1317:B 89 6 e1197:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1318:B 89 6 e1198:=viaPerm pt0 pti0 b1317 (by decide +kernel) (by decide +kernel)
theorem b1319:B 89 6 e1199:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1320:B 89 6 e1200:=viaPerm pt0 pti0 b1319 (by decide +kernel) (by decide +kernel)
theorem b1321:B 89 6 e1201:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1322:B 89 6 e1202:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1323:B 89 6 e1203:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1324:B 89 6 e1204:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1325:B 89 6 e1205:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1326:B 89 6 e1206:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1327:B 89 6 e1207:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1328:B 89 6 e1208:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1329:B 89 6 e1209:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1330:B 89 6 e1210:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1331:B 89 6 e1211:=viaPerm pt0 pti0 b1321 (by decide +kernel) (by decide +kernel)
theorem b1332:B 89 6 e1212:=viaPerm pt0 pti0 b1322 (by decide +kernel) (by decide +kernel)
theorem b1333:B 89 6 e1213:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1334:B 89 6 e1214:=viaCut pjt_11 w994 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1335:B 89 6 e1215:=viaCut pjt_11 w824 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1336:B 89 6 e1216:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1337:B 89 6 e1217:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1338:B 89 6 e1218:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1339:B 89 6 e1219:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1340:B 89 6 e1220:=viaPerm pt0 pti0 b1313 (by decide +kernel) (by decide +kernel)
theorem b1341:B 89 6 e1221:=viaPerm pt0 pti0 b1314 (by decide +kernel) (by decide +kernel)
theorem b1342:B 89 6 e1222:=viaPerm pt0 pti0 b1315 (by decide +kernel) (by decide +kernel)
theorem b1343:B 89 6 e1223:=viaPerm pt0 pti0 b1316 (by decide +kernel) (by decide +kernel)
theorem b1344:B 89 6 e1224:=viaPerm pt0 pti0 b1323 (by decide +kernel) (by decide +kernel)
theorem b1345:B 89 6 e1225:=viaPerm pt0 pti0 b1324 (by decide +kernel) (by decide +kernel)
theorem b1346:B 89 6 e1226:=viaPerm pt0 pti0 b1325 (by decide +kernel) (by decide +kernel)
theorem b1347:B 89 6 e1227:=viaPerm pt0 pti0 b1326 (by decide +kernel) (by decide +kernel)
theorem b1348:B 89 6 e1228:=viaPerm pt0 pti0 b1327 (by decide +kernel) (by decide +kernel)
theorem b1349:B 89 6 e1229:=viaPerm pt0 pti0 b1328 (by decide +kernel) (by decide +kernel)
theorem b1350:B 89 6 e1230:=viaPerm pt0 pti0 b1329 (by decide +kernel) (by decide +kernel)
theorem b1351:B 89 6 e1231:=viaPerm pt0 pti0 b1330 (by decide +kernel) (by decide +kernel)
theorem b1352:B 89 6 e1232:=viaPerm pt0 pti0 b1333 (by decide +kernel) (by decide +kernel)
theorem b1353:B 89 6 e1233:=viaPerm pt0 pti0 b1334 (by decide +kernel) (by decide +kernel)
theorem b1354:B 89 6 e1234:=viaPerm pt0 pti0 b1335 (by decide +kernel) (by decide +kernel)
theorem b1355:B 89 6 e1235:=viaPerm pt0 pti0 b1336 (by decide +kernel) (by decide +kernel)
theorem b1356:B 89 6 e1236:=viaPerm pt0 pti0 b1337 (by decide +kernel) (by decide +kernel)
theorem b1357:B 89 6 e1237:=viaPerm pt0 pti0 b1056 (by decide +kernel) (by decide +kernel)
theorem b1358:B 89 6 e1238:=viaPerm pt0 pti0 b1338 (by decide +kernel) (by decide +kernel)
theorem b1359:B 89 6 e1239:=viaPerm pt0 pti0 b1339 (by decide +kernel) (by decide +kernel)
theorem b1360:B 89 6 e1240:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1361:B 89 7 e1241:=viaBranch (ws:=[e1172,e1173,e1174,e1175,e1176,e806,e897,e808,e1177,e996,e1178,e1179,e1180,e1181,e1182,e1183,e1184,e1185,e1186,e1187,e1188,e1189,e1190,e1107,e1191,e1109,e1192,e1193,e1194,e1195,e1196,e1197,e1198,e1199,e1200,e1201,e1202,e1203,e1204,e1205,e1206,e1207,e1208,e1209,e1210,e1211,e1212,e1213,e1214,e1215,e1216,e1217,e950,e1218,e1219,e1220,e1221,e1222,e1223,e1224,e1225,e1226,e1227,e1228,e1229,e1230,e1231,e1232,e1233,e1234,e1235,e1236,e1237,e1238,e1239,e1240]) (consBan b1292 (consBan b1293 (consBan b1294 (consBan b1295 (consBan b1296 (consBan b891 (consBan b995 (consBan b893 (consBan b1297 (consBan b1106 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1301 (consBan b1302 (consBan b1303 (consBan b1304 (consBan b1305 (consBan b1306 (consBan b1307 (consBan b1308 (consBan b1309 (consBan b1310 (consBan b1225 (consBan b1311 (consBan b1227 (consBan b1312 (consBan b1313 (consBan b1314 (consBan b1315 (consBan b1316 (consBan b1317 (consBan b1318 (consBan b1319 (consBan b1320 (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1327 (consBan b1328 (consBan b1329 (consBan b1330 (consBan b1331 (consBan b1332 (consBan b1333 (consBan b1334 (consBan b1335 (consBan b1336 (consBan b1337 (consBan b1056 (consBan b1338 (consBan b1339 (consBan b1340 (consBan b1341 (consBan b1342 (consBan b1343 (consBan b1344 (consBan b1345 (consBan b1346 (consBan b1347 (consBan b1348 (consBan b1349 (consBan b1350 (consBan b1351 (consBan b1352 (consBan b1353 (consBan b1354 (consBan b1355 (consBan b1356 (consBan b1357 (consBan b1358 (consBan b1359 (consBan b1360 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1362:B 89 7 e1240:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1392:B 89 6 e1268:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1393:B 89 6 e1269:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1394:B 89 6 e1270:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1395:B 89 6 e1271:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1396:B 89 6 e1272:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1397:B 89 6 e1273:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1398:B 89 6 e1274:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1399:B 89 6 e1275:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1400:B 89 6 e1276:=viaPerm pt0 pti0 b1392 (by decide +kernel) (by decide +kernel)
theorem b1401:B 89 6 e1277:=viaPerm pt0 pti0 b1393 (by decide +kernel) (by decide +kernel)
theorem b1402:B 89 6 e1278:=viaPerm pt0 pti0 b1394 (by decide +kernel) (by decide +kernel)
theorem b1403:B 89 6 e1279:=viaPerm pt0 pti0 b525 (by decide +kernel) (by decide +kernel)
theorem b1404:B 89 6 e1280:=viaPerm pt0 pti0 b1395 (by decide +kernel) (by decide +kernel)
theorem b1405:B 89 6 e1281:=viaPerm pt0 pti0 b1396 (by decide +kernel) (by decide +kernel)
theorem b1406:B 89 6 e1282:=viaPerm pt0 pti0 b1397 (by decide +kernel) (by decide +kernel)
theorem b1407:B 89 6 e1283:=viaPerm pt0 pti0 b896 (by decide +kernel) (by decide +kernel)
theorem b1408:B 89 6 e1284:=viaPerm pt0 pti0 b998 (by decide +kernel) (by decide +kernel)
theorem b1409:B 89 6 e1285:=viaPerm pt0 pti0 b1398 (by decide +kernel) (by decide +kernel)
theorem b1410:B 89 6 e1286:=viaPerm pt0 pti0 b1108 (by decide +kernel) (by decide +kernel)
theorem b1411:B 89 6 e1287:=viaPerm pt0 pti0 b1399 (by decide +kernel) (by decide +kernel)
theorem b1412:B 89 6 e1171:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1413:B 89 6 e1288:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1418:B 20 4 e14:=viaSmall (by decide +kernel) (by decide)
theorem w1419:W 20 4 e14:=widen (by decide +kernel) b1418
theorem b1420:B 89 6 e1292:=viaCut pjt_11 w1419 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1421:B 89 6 e1293:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1422:B 89 6 e1294:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1423:B 89 6 e1295:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1424:B 89 6 e1296:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1425:B 89 6 e1297:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1426:B 89 6 e1298:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1427:B 89 6 e1299:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1428:B 89 6 e1300:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1429:B 89 6 e1301:=viaPerm pt0 pti0 b1428 (by decide +kernel) (by decide +kernel)
theorem b1430:B 89 6 e1302:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1431:B 89 6 e1303:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1432:B 89 6 e1304:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1433:B 89 6 e1305:=viaPerm pt0 pti0 b1431 (by decide +kernel) (by decide +kernel)
theorem b1434:B 89 6 e1306:=viaPerm pt0 pti0 b1432 (by decide +kernel) (by decide +kernel)
theorem b1435:B 89 6 e1307:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1436:B 89 6 e1308:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1437:B 89 6 e1309:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1438:B 89 6 e1310:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1439:B 89 6 e1311:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1440:B 89 6 e1312:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1441:B 89 6 e1313:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1442:B 89 6 e1314:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1443:B 89 6 e1315:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1444:B 89 6 e1316:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1445:B 89 6 e1317:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1446:B 89 6 e1318:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1447:B 89 6 e1319:=viaPerm pt0 pti0 b1435 (by decide +kernel) (by decide +kernel)
theorem b1448:B 89 6 e1320:=viaPerm pt0 pti0 b1436 (by decide +kernel) (by decide +kernel)
theorem b1449:B 89 6 e1321:=viaPerm pt0 pti0 b1437 (by decide +kernel) (by decide +kernel)
theorem b1450:B 89 6 e1322:=viaPerm pt0 pti0 b1439 (by decide +kernel) (by decide +kernel)
theorem b1451:B 89 6 e1323:=viaPerm pt0 pti0 b1440 (by decide +kernel) (by decide +kernel)
theorem b1452:B 89 6 e1324:=viaPerm pt0 pti0 b1438 (by decide +kernel) (by decide +kernel)
theorem w1453:W 20 3 e14:=widen (by decide +kernel) b28
theorem b1454:B 89 6 e1325:=viaCut pjt_15 w1453 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1455:B 20 4 e14:=viaPerm pc15_0 pci15_0 b1146 (by decide +kernel) (by decide +kernel)
theorem w1456:W 20 4 e14:=widen (by decide +kernel) b1455
theorem b1457:B 89 6 e1326:=viaCut pjt_15 w1456 (by decide) (by decide +kernel) (by decide +kernel)
theorem w1458:W 20 3 e14:=widen (by decide +kernel) b21
theorem b1459:B 89 6 e1327:=viaCut pjt_11 w1458 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1460:B 89 6 e1328:=viaPerm pt0 pti0 b1459 (by decide +kernel) (by decide +kernel)
theorem b1461:B 89 6 e1329:=viaCut pjt_11 w1458 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1462:B 89 6 e1330:=viaCut pjt_11 w1419 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1463:B 89 6 e1331:=viaCut pjt_11 w1458 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1464:B 89 6 e1332:=viaCut pjt_11 w1419 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1465:B 89 6 e1333:=viaPerm pt0 pti0 b1413 (by decide +kernel) (by decide +kernel)
theorem b1466:B 89 6 e1334:=viaPerm pt0 pti0 b1420 (by decide +kernel) (by decide +kernel)
theorem b1467:B 89 6 e1335:=viaPerm pt0 pti0 b1421 (by decide +kernel) (by decide +kernel)
theorem b1468:B 89 6 e1336:=viaPerm pt0 pti0 b1422 (by decide +kernel) (by decide +kernel)
theorem b1469:B 89 6 e1337:=viaPerm pt0 pti0 b1423 (by decide +kernel) (by decide +kernel)
theorem b1470:B 89 6 e1338:=viaPerm pt0 pti0 b1424 (by decide +kernel) (by decide +kernel)
theorem b1471:B 89 6 e1339:=viaPerm pt0 pti0 b1425 (by decide +kernel) (by decide +kernel)
theorem b1472:B 89 6 e1340:=viaPerm pt0 pti0 b1426 (by decide +kernel) (by decide +kernel)
theorem b1473:B 89 6 e1341:=viaPerm pt0 pti0 b1441 (by decide +kernel) (by decide +kernel)
theorem b1474:B 89 6 e1342:=viaPerm pt0 pti0 b1442 (by decide +kernel) (by decide +kernel)
theorem b1475:B 89 6 e1343:=viaPerm pt0 pti0 b1443 (by decide +kernel) (by decide +kernel)
theorem b1476:B 89 6 e1344:=viaPerm pt0 pti0 b1444 (by decide +kernel) (by decide +kernel)
theorem b1477:B 89 6 e1345:=viaPerm pt0 pti0 b1445 (by decide +kernel) (by decide +kernel)
theorem b1478:B 89 6 e1346:=viaPerm pt0 pti0 b1446 (by decide +kernel) (by decide +kernel)
theorem b1479:B 89 6 e1347:=viaPerm pt0 pti0 b1461 (by decide +kernel) (by decide +kernel)
theorem b1480:B 89 6 e1348:=viaPerm pt0 pti0 b1462 (by decide +kernel) (by decide +kernel)
theorem b1481:B 89 6 e1349:=viaPerm pt0 pti0 b1463 (by decide +kernel) (by decide +kernel)
theorem b1482:B 89 6 e1350:=viaPerm pt0 pti0 b1464 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1483:B 89 7 e1108:=viaBranch (ws:=[e1268,e1269,e1270,e470,e1271,e1272,e1273,e810,e900,e1274,e998,e1275,e1276,e1277,e1278,e1279,e1280,e1281,e1282,e1283,e1284,e1285,e1286,e1287,e1107,e1171,e1109,e1288,e1292,e1293,e1294,e1295,e1296,e1297,e1298,e1299,e1300,e1301,e1302,e1303,e1304,e1305,e1306,e1307,e1308,e1309,e1310,e1311,e1312,e1313,e1314,e1315,e1316,e1317,e1318,e1319,e1320,e1321,e1322,e1323,e1324,e1325,e1326,e1327,e1328,e1329,e1330,e1331,e1332,e1333,e1334,e1335,e1336,e1337,e1338,e1339,e1340,e1341,e1342,e1343,e1344,e1345,e1346,e1347,e1348,e1349,e1350]) (consBan b1392 (consBan b1393 (consBan b1394 (consBan b525 (consBan b1395 (consBan b1396 (consBan b1397 (consBan b896 (consBan b998 (consBan b1398 (consBan b1108 (consBan b1399 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b1404 (consBan b1405 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b1409 (consBan b1410 (consBan b1411 (consBan b1225 (consBan b1412 (consBan b1227 (consBan b1413 (consBan b1420 (consBan b1421 (consBan b1422 (consBan b1423 (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1434 (consBan b1435 (consBan b1436 (consBan b1437 (consBan b1438 (consBan b1439 (consBan b1440 (consBan b1441 (consBan b1442 (consBan b1443 (consBan b1444 (consBan b1445 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1451 (consBan b1452 (consBan b1454 (consBan b1457 (consBan b1459 (consBan b1460 (consBan b1461 (consBan b1462 (consBan b1463 (consBan b1464 (consBan b1465 (consBan b1466 (consBan b1467 (consBan b1468 (consBan b1469 (consBan b1470 (consBan b1471 (consBan b1472 (consBan b1473 (consBan b1474 (consBan b1475 (consBan b1476 (consBan b1477 (consBan b1478 (consBan b1479 (consBan b1480 (consBan b1481 (consBan b1482 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1484:B 89 6 e1351:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1485:B 89 6 e1352:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1486:B 89 6 e1353:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1487:B 89 6 e1354:=viaPerm pt0 pti0 b1484 (by decide +kernel) (by decide +kernel)
theorem b1488:B 89 6 e1355:=viaPerm pt0 pti0 b1485 (by decide +kernel) (by decide +kernel)
theorem b1489:B 89 6 e1356:=viaPerm pt0 pti0 b526 (by decide +kernel) (by decide +kernel)
theorem b1490:B 89 6 e1357:=viaPerm pt0 pti0 b1486 (by decide +kernel) (by decide +kernel)
theorem b1491:B 89 6 e1358:=viaPerm pt0 pti0 b897 (by decide +kernel) (by decide +kernel)
theorem b1492:B 89 6 e1359:=viaPerm pt0 pti0 b1109 (by decide +kernel) (by decide +kernel)
theorem b1493:B 89 6 e1241:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1494:B 89 6 e1360:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1495:B 89 6 e1361:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1496:B 89 6 e1362:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1497:B 16 3 e1363:=viaSmall (by decide +kernel) (by decide)
theorem w1498:W 16 3 e1363:=widen (by decide +kernel) b1497
theorem b1499:B 89 6 e1364:=viaCut pjt_13 w1498 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1500:B 89 6 e1365:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1501:B 89 6 e1366:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1502:B 89 6 e1367:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1503:B 89 6 e1368:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1504:B 89 6 e1369:=viaPerm pt0 pti0 b1503 (by decide +kernel) (by decide +kernel)
theorem b1505:B 89 6 e1370:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1506:B 89 6 e1371:=viaPerm pt0 pti0 b1505 (by decide +kernel) (by decide +kernel)
theorem b1507:B 89 6 e1372:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1508:B 89 6 e1373:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1509:B 89 6 e1374:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1510:B 89 6 e1375:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1511:B 89 6 e1376:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1512:B 89 6 e1377:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1513:B 89 6 e1378:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1514:B 89 6 e1379:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1515:B 89 6 e1380:=viaPerm pt0 pti0 b1507 (by decide +kernel) (by decide +kernel)
theorem b1516:B 89 6 e1381:=viaPerm pt0 pti0 b1508 (by decide +kernel) (by decide +kernel)
theorem b1517:B 89 6 e1382:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1518:B 20 4 e1383:=viaSmall (by decide +kernel) (by decide)
theorem w1519:W 20 4 e1383:=viaSub (ws:=[e126,e1383]) (consBan b147 (consBan b1518 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1520:B 89 6 e1384:=viaCut pjt_15 w1519 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1521:B 89 6 e1385:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1522:B 20 4 e1386:=viaSmall (by decide +kernel) (by decide)
theorem w1523:W 20 4 e1386:=viaSub (ws:=[e14,e126,e1386]) (consBan b1418 (consBan b868 (consBan b1522 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1524:B 89 6 e1387:=viaCut pjt_11 w1523 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1525:B 89 6 e1388:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1526:B 89 6 e1389:=viaPerm pt0 pti0 b1499 (by decide +kernel) (by decide +kernel)
theorem b1527:B 89 6 e1390:=viaPerm pt0 pti0 b1500 (by decide +kernel) (by decide +kernel)
theorem b1528:B 89 6 e1391:=viaPerm pt0 pti0 b1501 (by decide +kernel) (by decide +kernel)
theorem b1529:B 89 6 e1392:=viaPerm pt0 pti0 b1502 (by decide +kernel) (by decide +kernel)
theorem b1530:B 89 6 e1393:=viaPerm pt0 pti0 b1509 (by decide +kernel) (by decide +kernel)
theorem b1531:B 89 6 e1394:=viaPerm pt0 pti0 b1510 (by decide +kernel) (by decide +kernel)
theorem b1532:B 89 6 e1395:=viaPerm pt0 pti0 b1511 (by decide +kernel) (by decide +kernel)
theorem b1533:B 89 6 e1396:=viaPerm pt0 pti0 b1512 (by decide +kernel) (by decide +kernel)
theorem b1534:B 89 6 e1397:=viaPerm pt0 pti0 b1513 (by decide +kernel) (by decide +kernel)
theorem b1535:B 89 6 e1398:=viaPerm pt0 pti0 b1514 (by decide +kernel) (by decide +kernel)
theorem b1536:B 89 6 e1399:=viaPerm pt0 pti0 b1517 (by decide +kernel) (by decide +kernel)
theorem b1537:B 89 6 e1400:=viaPerm pt0 pti0 b1520 (by decide +kernel) (by decide +kernel)
theorem b1538:B 89 6 e1401:=viaPerm pt0 pti0 b1521 (by decide +kernel) (by decide +kernel)
theorem b1539:B 89 6 e1402:=viaPerm pt0 pti0 b1058 (by decide +kernel) (by decide +kernel)
theorem b1540:B 89 6 e1403:=viaPerm pt0 pti0 b1524 (by decide +kernel) (by decide +kernel)
theorem b1541:B 89 6 e1404:=viaPerm pt0 pti0 b1525 (by decide +kernel) (by decide +kernel)
theorem b1542:B 89 6 e1082:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1543:B 89 7 e1192:=viaBranch (ws:=[e1351,e1352,e471,e1353,e811,e999,e1354,e1355,e1356,e1357,e1358,e1359,e1191,e1241,e1360,e1107,e1109,e1361,e1362,e1364,e1365,e1366,e1367,e1368,e1369,e1370,e1371,e1372,e1373,e1374,e1375,e1376,e1377,e1313,e1378,e1316,e1379,e1380,e1381,e1382,e1384,e1385,e952,e1329,e1387,e1331,e1388,e1389,e1390,e1391,e1392,e1393,e1394,e1395,e1396,e1341,e1397,e1344,e1398,e1399,e1400,e1401,e1402,e1347,e1403,e1349,e1404,e1082]) (consBan b1484 (consBan b1485 (consBan b526 (consBan b1486 (consBan b897 (consBan b1109 (consBan b1487 (consBan b1488 (consBan b1489 (consBan b1490 (consBan b1491 (consBan b1492 (consBan b1311 (consBan b1493 (consBan b1494 (consBan b1225 (consBan b1227 (consBan b1495 (consBan b1496 (consBan b1499 (consBan b1500 (consBan b1501 (consBan b1502 (consBan b1503 (consBan b1504 (consBan b1505 (consBan b1506 (consBan b1507 (consBan b1508 (consBan b1509 (consBan b1510 (consBan b1511 (consBan b1512 (consBan b1441 (consBan b1513 (consBan b1444 (consBan b1514 (consBan b1515 (consBan b1516 (consBan b1517 (consBan b1520 (consBan b1521 (consBan b1058 (consBan b1461 (consBan b1524 (consBan b1463 (consBan b1525 (consBan b1526 (consBan b1527 (consBan b1528 (consBan b1529 (consBan b1530 (consBan b1531 (consBan b1532 (consBan b1533 (consBan b1473 (consBan b1534 (consBan b1476 (consBan b1535 (consBan b1536 (consBan b1537 (consBan b1538 (consBan b1539 (consBan b1479 (consBan b1540 (consBan b1481 (consBan b1541 (consBan b1542 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1544:B 89 7 e1405:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1552:B 35 5 e1411:=viaSmall (by decide +kernel) (by decide)
theorem b1567:B 40 6 e1426:=viaPerm pc1_1 pci1_1 b429 (by decide +kernel) (by decide +kernel)
theorem w1568:W 40 6 e1426:=widen (by decide +kernel) b1567
theorem b1569:B 89 7 e1427:=viaCut pjt_1 w1568 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1590:B 89 6 e1447:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1591:B 89 6 e1448:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1592:B 89 6 e1449:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1593:B 89 6 e1450:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1594:B 89 6 e1451:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1595:B 89 6 e1452:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1596:B 89 6 e1453:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1597:B 89 6 e1454:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1598:B 89 6 e1455:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1599:B 89 6 e1456:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1600:B 89 6 e1457:=viaPerm pt0 pti0 b359 (by decide +kernel) (by decide +kernel)
theorem b1601:B 89 6 e1458:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1602:B 89 6 e1459:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1603:B 89 6 e1460:=viaPerm pt0 pti0 b570 (by decide +kernel) (by decide +kernel)
theorem b1604:B 89 6 e1461:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1605:B 89 6 e1462:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1606:B 89 6 e1463:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1607:B 89 6 e1464:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1608:B 89 6 e1465:=viaPerm pt0 pti0 b944 (by decide +kernel) (by decide +kernel)
theorem b1609:B 89 6 e1466:=viaPerm pt0 pti0 b1062 (by decide +kernel) (by decide +kernel)
theorem b1610:B 89 6 e1467:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1611:B 89 6 e1468:=viaPerm pt0 pti0 b1165 (by decide +kernel) (by decide +kernel)
theorem b1612:B 89 6 e1469:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1613:B 89 6 e1470:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1614:B 89 6 e1471:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1615:B 89 6 e1472:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1616:B 89 6 e1473:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1617:B 89 6 e1474:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1618:B 89 6 e1475:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1619:B 89 6 e1476:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1620:B 89 6 e1477:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1621:B 89 6 e1478:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1622:B 89 6 e1479:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1623:B 89 6 e1480:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1624:B 89 6 e1481:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1625:B 89 6 e1482:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1626:B 89 6 e1483:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1627:B 89 6 e1484:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1628:B 89 6 e1485:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1629:B 89 6 e1486:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1630:B 89 6 e1487:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1631:B 35 5 e1488:=viaSmall (by decide +kernel) (by decide)
theorem w1632:W 35 5 e1488:=widen (by decide +kernel) b1631
theorem b1633:B 89 6 e1489:=viaCut pjt_0 w1632 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1634:B 89 6 e1490:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1635:B 89 6 e1491:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1636:B 89 6 e1492:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1637:B 89 6 e1493:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1638:B 89 6 e1494:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1639:B 89 6 e1495:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1640:B 89 6 e1496:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1641:B 89 6 e1497:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1642:B 89 6 e1498:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1643:B 89 6 e1499:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1644:B 89 6 e1500:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1645:B 89 6 e1501:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1646:B 89 6 e1502:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1647:B 89 6 e1503:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1648:B 89 6 e1504:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1652:B 40 5 e1507:=viaSmall (by decide +kernel) (by decide)
theorem b1653:B 40 5 e1508:=viaSmall (by decide +kernel) (by decide)
theorem w1654:W 40 5 e1508:=viaSub (ws:=[e1507,e1508]) (consBan b1652 (consBan b1653 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1655:B 89 6 e1509:=viaCut pjt_2 w1654 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1656:B 89 6 e1510:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1657:B 89 6 e1511:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1658:B 89 6 e1512:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1659:B 89 6 e1513:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1660:B 89 6 e1514:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1661:B 89 6 e1515:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1662:B 89 6 e1516:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1663:B 89 6 e1517:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1664:B 89 6 e1518:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1665:B 89 6 e1519:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1666:B 89 6 e1520:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1667:B 89 6 e1521:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1668:B 89 6 e1522:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1669:B 89 6 e1523:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1670:B 89 6 e1524:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1671:B 89 6 e1525:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1672:B 89 6 e1526:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1673:B 89 6 e1527:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1674:B 89 6 e1528:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1675:B 89 6 e1529:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1676:B 89 7 e1530:=viaBranch (ws:=[e1447,e80,e1448,e474,e1449,e1450,e1451,e813,e1452,e1453,e1454,e1455,e1456,e1457,e1458,e1459,e1460,e1461,e1462,e1463,e1464,e1465,e1466,e1467,e1468,e1469,e1470,e1113,e1194,e1471,e1293,e1365,e1472,e1473,e1474,e1475,e1476,e1477,e1478,e1479,e1480,e1481,e1482,e1483,e1484,e1485,e1486,e1487,e1489,e1490,e1491,e1492,e1493,e1494,e1495,e1496,e1497,e1498,e1499,e1500,e1501,e1502,e1503,e1504,e1509,e1510,e1511,e1512,e1513,e1514,e1515,e1516,e1517,e1518,e1519,e1520,e1521,e1522,e1523,e1524,e1525,e1526,e1527,e1528,e1529]) (consBan b1590 (consBan b98 (consBan b1591 (consBan b530 (consBan b1592 (consBan b1593 (consBan b1594 (consBan b899 (consBan b1595 (consBan b1596 (consBan b1597 (consBan b1598 (consBan b1599 (consBan b1600 (consBan b1601 (consBan b1602 (consBan b1603 (consBan b1604 (consBan b1605 (consBan b1606 (consBan b1607 (consBan b1608 (consBan b1609 (consBan b1610 (consBan b1611 (consBan b1612 (consBan b1613 (consBan b1232 (consBan b1314 (consBan b1614 (consBan b1421 (consBan b1500 (consBan b1615 (consBan b1616 (consBan b1617 (consBan b1618 (consBan b1619 (consBan b1620 (consBan b1621 (consBan b1622 (consBan b1623 (consBan b1624 (consBan b1625 (consBan b1626 (consBan b1627 (consBan b1628 (consBan b1629 (consBan b1630 (consBan b1633 (consBan b1634 (consBan b1635 (consBan b1636 (consBan b1637 (consBan b1638 (consBan b1639 (consBan b1640 (consBan b1641 (consBan b1642 (consBan b1643 (consBan b1644 (consBan b1645 (consBan b1646 (consBan b1647 (consBan b1648 (consBan b1655 (consBan b1656 (consBan b1657 (consBan b1658 (consBan b1659 (consBan b1660 (consBan b1661 (consBan b1662 (consBan b1663 (consBan b1664 (consBan b1665 (consBan b1666 (consBan b1667 (consBan b1668 (consBan b1669 (consBan b1670 (consBan b1671 (consBan b1672 (consBan b1673 (consBan b1674 (consBan b1675 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1677:B 89 6 e1531:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1678:B 89 6 e1532:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1679:B 89 6 e1533:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1680:B 89 6 e1534:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1681:B 89 6 e1535:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1682:B 89 6 e1536:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1683:B 89 6 e1537:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1684:B 89 6 e1538:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1685:B 89 6 e1539:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1686:B 89 6 e1540:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1687:B 89 6 e1541:=viaPerm pt0 pti0 b360 (by decide +kernel) (by decide +kernel)
theorem b1688:B 89 6 e1542:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1689:B 89 6 e1543:=viaPerm pt0 pti0 b571 (by decide +kernel) (by decide +kernel)
theorem b1690:B 89 6 e1544:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1691:B 89 6 e1545:=viaPerm pt0 pti0 b945 (by decide +kernel) (by decide +kernel)
theorem b1692:B 89 6 e1546:=viaPerm pt0 pti0 b1166 (by decide +kernel) (by decide +kernel)
theorem b1693:B 89 6 e1547:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1694:B 89 6 e1548:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1695:B 89 6 e1549:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1696:B 89 6 e1550:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1697:B 89 6 e1551:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1698:B 89 6 e1552:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1699:B 89 6 e1553:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1700:B 89 6 e1554:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1701:B 89 6 e1555:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1702:B 89 6 e1556:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1703:B 89 6 e1557:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1704:B 89 6 e1558:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1705:B 89 6 e1559:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1706:B 89 6 e1560:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1707:B 89 6 e1561:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1708:B 89 6 e1562:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1709:B 89 6 e1563:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1710:B 89 6 e1564:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1711:B 12 4 e1565:=viaSmall (by decide +kernel) (by decide)
theorem w1712:W 12 4 e1565:=widen (by decide +kernel) b1711
theorem b1713:B 89 6 e1566:=viaCut pjt_10 w1712 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1714:B 16 3 e1363:=viaSmall (by decide +kernel) (by decide)
theorem w1715:W 16 3 e1363:=widen (by decide +kernel) b1714
theorem b1716:B 89 6 e1567:=viaCut pjt_12 w1715 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1717:B 89 6 e1568:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1718:B 89 6 e1569:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1719:B 20 4 e935:=viaPerm pc11_2 pci11_2 b819 (by decide +kernel) (by decide +kernel)
theorem b1720:B 20 4 e936:=viaPerm pc11_2 pci11_2 b993 (by decide +kernel) (by decide +kernel)
theorem w1721:W 20 4 e936:=viaSub (ws:=[e126,e935,e936]) (consBan b868 (consBan b1719 (consBan b1720 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1722:B 89 6 e1570:=viaCut pjt_11 w1721 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1723:B 89 6 e1571:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1724:B 89 6 e1572:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1725:B 16 4 e1573:=viaSmall (by decide +kernel) (by decide)
theorem w1726:W 16 4 e1573:=widen (by decide +kernel) b1725
theorem b1727:B 89 6 e1574:=viaCut pjt_9 w1726 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1728:B 89 6 e1575:=viaCut pjt_13 w1498 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1729:B 89 6 e1576:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1730:B 89 6 e1577:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1731:B 89 6 e1578:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1732:B 89 6 e1579:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1733:B 89 6 e1580:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1734:B 89 6 e1581:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1735:B 89 6 e1582:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1736:B 89 6 e1583:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1737:B 89 6 e1584:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1738:B 89 6 e1585:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1739:B 89 6 e1586:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1747:B 89 6 e1594:=viaCut pjt_2 w1654 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1748:B 89 6 e1595:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1749:B 89 6 e1596:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1750:B 89 6 e1597:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1751:B 89 6 e1598:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1752:B 89 6 e1599:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1753:B 89 6 e1600:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1754:B 89 6 e1601:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1755:B 89 6 e1602:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1756:B 89 6 e1603:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1757:B 89 6 e1604:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1758:B 89 6 e1605:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1759:B 89 6 e1606:=viaCut pjt_11 w1721 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1760:B 89 6 e1607:=viaCut pjt_18 w352 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1761:B 89 6 e1608:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1762:B 16 3 e1363:=viaSmall (by decide +kernel) (by decide)
theorem w1763:W 16 3 e1363:=widen (by decide +kernel) b1762
theorem b1764:B 89 6 e1609:=viaCut pjt_14 w1763 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1765:B 89 6 e1610:=viaPerm pt0 pti0 b1661 (by decide +kernel) (by decide +kernel)
theorem b1766:B 89 6 e1611:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1767:B 89 6 e1612:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1768:B 89 6 e1613:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1769:B 89 6 e1614:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1770:B 89 7 e1615:=viaBranch (ws:=[e1531,e81,e1532,e473,e475,e1533,e1534,e1535,e903,e1536,e1537,e1538,e912,e1539,e1540,e1541,e1542,e1543,e1544,e1545,e1546,e1114,e1294,e1547,e1548,e1549,e1550,e1551,e1472,e1552,e1474,e1553,e1554,e1555,e1556,e1557,e1558,e1559,e1560,e1561,e1562,e1563,e1564,e1566,e1567,e1568,e1569,e1570,e1571,e1572,e1574,e1575,e1576,e1577,e1578,e1579,e1580,e1581,e1582,e1583,e1584,e1585,e1586,e1594,e1595,e1596,e1597,e1598,e1599,e1600,e1601,e1602,e1603,e1604,e1605,e1606,e1607,e1608,e1609,e1610,e1611,e1612,e1613,e1614]) (consBan b1677 (consBan b99 (consBan b1678 (consBan b529 (consBan b531 (consBan b1679 (consBan b1680 (consBan b1681 (consBan b1001 (consBan b1682 (consBan b1683 (consBan b1684 (consBan b1011 (consBan b1685 (consBan b1686 (consBan b1687 (consBan b1688 (consBan b1689 (consBan b1690 (consBan b1691 (consBan b1692 (consBan b1233 (consBan b1422 (consBan b1693 (consBan b1694 (consBan b1695 (consBan b1696 (consBan b1697 (consBan b1615 (consBan b1698 (consBan b1617 (consBan b1699 (consBan b1700 (consBan b1701 (consBan b1702 (consBan b1703 (consBan b1704 (consBan b1705 (consBan b1706 (consBan b1707 (consBan b1708 (consBan b1709 (consBan b1710 (consBan b1713 (consBan b1716 (consBan b1717 (consBan b1718 (consBan b1722 (consBan b1723 (consBan b1724 (consBan b1727 (consBan b1728 (consBan b1729 (consBan b1730 (consBan b1731 (consBan b1732 (consBan b1733 (consBan b1734 (consBan b1735 (consBan b1736 (consBan b1737 (consBan b1738 (consBan b1739 (consBan b1747 (consBan b1748 (consBan b1749 (consBan b1750 (consBan b1751 (consBan b1752 (consBan b1753 (consBan b1754 (consBan b1755 (consBan b1756 (consBan b1757 (consBan b1758 (consBan b1759 (consBan b1760 (consBan b1761 (consBan b1764 (consBan b1765 (consBan b1766 (consBan b1767 (consBan b1768 (consBan b1769 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1790:B 40 6 e1635:=viaPerm pc1_1 pci1_1 b640 (by decide +kernel) (by decide +kernel)
theorem w1791:W 40 6 e1635:=widen (by decide +kernel) b1790
theorem b1792:B 89 7 e1636:=viaCut pjt_1 w1791 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1793:B 89 7 e1577:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1826:B 89 6 e1666:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1827:B 89 6 e1667:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1828:B 89 6 e1668:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1829:B 89 6 e1669:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1830:B 89 6 e1670:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1831:B 89 6 e1671:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1832:B 89 6 e1672:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1833:B 89 6 e1673:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1834:B 89 6 e1674:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1835:B 89 6 e1675:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1836:B 89 6 e1676:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1837:B 89 6 e1677:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1838:B 89 6 e1678:=viaPerm pt0 pti0 b363 (by decide +kernel) (by decide +kernel)
theorem b1839:B 89 6 e1679:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1840:B 89 6 e1680:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1841:B 89 6 e1681:=viaPerm pt0 pti0 b574 (by decide +kernel) (by decide +kernel)
theorem b1842:B 89 6 e1682:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1843:B 89 6 e1683:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1844:B 89 6 e1684:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1845:B 89 6 e1685:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1846:B 89 6 e1686:=viaPerm pt0 pti0 b948 (by decide +kernel) (by decide +kernel)
theorem b1847:B 89 6 e1687:=viaPerm pt0 pti0 b1064 (by decide +kernel) (by decide +kernel)
theorem b1848:B 89 6 e1688:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1849:B 89 6 e1689:=viaPerm pt0 pti0 b1169 (by decide +kernel) (by decide +kernel)
theorem b1850:B 89 6 e1690:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1851:B 89 6 e1691:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1852:B 89 6 e1692:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1853:B 89 6 e1530:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1854:B 89 6 e1693:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1855:B 89 6 e1694:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1856:B 89 6 e1695:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1857:B 89 6 e1696:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1858:B 89 6 e1697:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1859:B 89 6 e1698:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1860:B 89 6 e1699:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1861:B 89 6 e1700:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1862:B 89 6 e1701:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1863:B 89 6 e1702:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1864:B 89 6 e1703:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1865:B 89 6 e1704:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1866:B 89 6 e1705:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1867:B 89 6 e1706:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1868:B 89 6 e1707:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1869:B 89 6 e1708:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1870:B 89 6 e1709:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1871:B 89 6 e1710:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1872:B 89 6 e1711:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1873:B 89 6 e1712:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1874:B 89 6 e1713:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1875:B 89 6 e1714:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1876:B 89 6 e1715:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1877:B 89 6 e1716:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1878:B 89 6 e1717:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1879:B 89 6 e1718:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1880:B 89 6 e1719:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1881:B 89 6 e1720:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1882:B 89 6 e1721:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1883:B 89 6 e1722:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1884:B 89 6 e1723:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1885:B 89 6 e1724:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1886:B 89 6 e1725:=viaPerm pt0 pti0 b1664 (by decide +kernel) (by decide +kernel)
theorem b1887:B 89 6 e1726:=viaPerm pt0 pti0 b1767 (by decide +kernel) (by decide +kernel)
theorem b1888:B 89 6 e1727:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1889:B 89 6 e1728:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1890:B 89 6 e1729:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1891:B 89 6 e1730:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1892:B 89 6 e1731:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1893:B 89 6 e1732:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1894:B 89 6 e1733:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1895:B 89 6 e1734:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1896:B 89 6 e1735:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1897:B 89 6 e1736:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1898:B 89 6 e1737:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1899:B 89 6 e1738:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1900:B 89 6 e1739:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1901:B 89 6 e1740:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1902:B 89 7 e1473:=viaBranch (ws:=[e1666,e1667,e1668,e1669,e1006,e1670,e1671,e144,e146,e1672,e1673,e478,e1674,e1675,e1676,e1677,e1678,e1679,e1680,e1681,e1682,e1683,e1684,e1685,e1686,e1687,e1688,e1689,e1690,e1691,e1117,e1196,e1692,e1297,e1367,e1530,e1472,e1474,e1693,e1694,e1695,e1696,e1697,e1698,e1699,e1700,e1701,e1702,e1703,e1704,e1705,e1706,e1707,e1708,e1709,e1710,e1711,e1712,e1713,e1714,e1715,e1716,e1717,e1718,e1719,e1720,e1721,e1722,e1723,e1724,e1725,e1726,e1727,e1728,e1729,e1730,e1731,e1732,e1733,e1734,e1735,e1736,e1737,e1738,e1739,e1740]) (consBan b1826 (consBan b1827 (consBan b1828 (consBan b1829 (consBan b1116 (consBan b1830 (consBan b1831 (consBan b168 (consBan b170 (consBan b1832 (consBan b1833 (consBan b534 (consBan b1834 (consBan b1835 (consBan b1836 (consBan b1837 (consBan b1838 (consBan b1839 (consBan b1840 (consBan b1841 (consBan b1842 (consBan b1843 (consBan b1844 (consBan b1845 (consBan b1846 (consBan b1847 (consBan b1848 (consBan b1849 (consBan b1850 (consBan b1851 (consBan b1236 (consBan b1316 (consBan b1852 (consBan b1425 (consBan b1502 (consBan b1853 (consBan b1615 (consBan b1617 (consBan b1854 (consBan b1855 (consBan b1856 (consBan b1857 (consBan b1858 (consBan b1859 (consBan b1860 (consBan b1861 (consBan b1862 (consBan b1863 (consBan b1864 (consBan b1865 (consBan b1866 (consBan b1867 (consBan b1868 (consBan b1869 (consBan b1870 (consBan b1871 (consBan b1872 (consBan b1873 (consBan b1874 (consBan b1875 (consBan b1876 (consBan b1877 (consBan b1878 (consBan b1879 (consBan b1880 (consBan b1881 (consBan b1882 (consBan b1883 (consBan b1884 (consBan b1885 (consBan b1886 (consBan b1887 (consBan b1888 (consBan b1889 (consBan b1890 (consBan b1891 (consBan b1892 (consBan b1893 (consBan b1894 (consBan b1895 (consBan b1896 (consBan b1897 (consBan b1898 (consBan b1899 (consBan b1900 (consBan b1901 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1903:B 89 7 e1553:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1904:B 89 7 e1741:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1940:B 89 6 e1776:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1941:B 89 6 e1777:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1942:B 89 6 e1778:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1943:B 89 6 e1779:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1944:B 89 6 e1780:=viaPerm pt0 pti0 b230 (by decide +kernel) (by decide +kernel)
theorem b1945:B 89 6 e1781:=viaPerm pt0 pti0 b232 (by decide +kernel) (by decide +kernel)
theorem b1946:B 89 6 e1782:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1947:B 89 6 e1783:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1948:B 89 6 e1784:=viaPerm pt0 pti0 b538 (by decide +kernel) (by decide +kernel)
theorem b1949:B 89 6 e1785:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1950:B 89 6 e1786:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1951:B 89 6 e1787:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1952:B 89 6 e1788:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1953:B 89 6 e1789:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1954:B 89 6 e1790:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1955:B 89 6 e1791:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1956:B 89 6 e1792:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1957:B 89 6 e1793:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1958:B 89 6 e1794:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1959:B 89 6 e1795:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1960:B 89 6 e1796:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1961:B 89 6 e1797:=viaPerm pt0 pti0 b906 (by decide +kernel) (by decide +kernel)
theorem b1962:B 89 6 e1798:=viaPerm pt0 pti0 b1017 (by decide +kernel) (by decide +kernel)
theorem b1963:B 89 6 e1799:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1964:B 89 6 e1800:=viaPerm pt0 pti0 b1120 (by decide +kernel) (by decide +kernel)
theorem b1965:B 89 6 e1801:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1966:B 89 6 e1802:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1967:B 89 6 e1803:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1968:B 89 6 e1804:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1969:B 89 6 e1805:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1970:B 89 6 e1806:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1971:B 89 6 e1807:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1972:B 89 6 e1808:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1973:B 89 6 e1809:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1974:B 89 6 e1810:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1975:B 89 6 e1811:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1976:B 89 6 e1812:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1977:B 89 6 e1813:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1978:B 16 3 e1814:=viaSmall (by decide +kernel) (by decide)
theorem w1979:W 16 3 e1814:=widen (by decide +kernel) b1978
theorem b1980:B 89 6 e1815:=viaCut pjt_9 w1979 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1981:B 89 6 e1816:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1982:B 89 6 e1817:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1983:B 89 6 e1818:=viaCut pjt_9 w1979 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1984:B 89 6 e1819:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1985:B 89 6 e1820:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1986:B 89 6 e1821:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1987:B 89 6 e1822:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1988:B 89 6 e1823:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1989:B 89 6 e1824:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1990:B 89 6 e1825:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1991:B 89 6 e1826:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1992:B 89 6 e1827:=viaPerm pt0 pti0 b1619 (by decide +kernel) (by decide +kernel)
theorem b1993:B 89 6 e1828:=viaPerm pt0 pti0 b1702 (by decide +kernel) (by decide +kernel)
theorem b1994:B 89 6 e1829:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1995:B 89 6 e1830:=viaPerm pt0 pti0 b1870 (by decide +kernel) (by decide +kernel)
theorem b1996:B 89 6 e1831:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1997:B 89 6 e1832:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1998:B 35 5 e1833:=viaSmall (by decide +kernel) (by decide)
theorem w1999:W 35 5 e1833:=widen (by decide +kernel) b1998
theorem b2000:B 89 6 e1834:=viaCut pjt_0 w1999 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2001:B 89 6 e1835:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2002:B 89 6 e1836:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2003:B 89 6 e1837:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2004:B 89 6 e1838:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2005:B 89 6 e1839:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2006:B 89 6 e1840:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2007:B 89 6 e1841:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2008:B 89 6 e1842:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2009:B 89 6 e1843:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2010:B 89 6 e1844:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2011:B 89 6 e1845:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2012:B 89 6 e1846:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2013:B 89 6 e1847:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2014:B 89 6 e1848:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2015:B 89 6 e1849:=viaCut pjt_9 w1979 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2044:B 35 5 e1877:=viaSmall (by decide +kernel) (by decide)
theorem b2045:B 35 5 e1878:=viaSmall (by decide +kernel) (by decide)
theorem b2046:B 35 5 e1879:=viaSmall (by decide +kernel) (by decide)
theorem w2047:W 35 5 e1879:=viaSub (ws:=[e1877,e1878,e1879]) (consBan b2044 (consBan b2045 (consBan b2046 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2048:B 89 6 e1880:=viaCut pjt_0 w2047 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2049:B 89 6 e1881:=viaCut pjt_9 w1979 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2050:B 12 3 e1882:=viaPerm pc18_1 pci18_1 b354 (by decide +kernel) (by decide +kernel)
theorem w2051:W 12 3 e1882:=viaSub (ws:=[e16,e1882]) (consBan b30 (consBan b2050 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2052:B 89 6 e1883:=viaCut pjt_18 w2051 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2053:B 89 7 e1884:=viaBranch (ws:=[e1776,e819,e917,e1777,e1009,e1778,e1779,e1780,e1781,e1782,e1783,e1784,e1785,e1786,e1787,e1788,e1789,e1790,e1791,e1792,e1793,e1794,e1795,e1796,e1797,e1798,e1799,e1800,e1801,e1802,e1120,e1197,e1803,e1300,e1368,e1804,e1805,e1806,e1807,e1808,e1809,e1810,e1811,e1812,e1813,e1815,e1816,e1817,e1818,e1819,e1820,e1821,e1822,e1823,e1824,e1825,e1826,e1827,e1828,e1829,e1830,e1831,e1832,e1834,e1835,e1836,e1837,e1838,e1839,e1840,e1841,e1842,e1843,e1844,e1845,e1846,e1847,e1848,e1849,e1880,e1881,e1883]) (consBan b1940 (consBan b905 (consBan b1016 (consBan b1941 (consBan b1119 (consBan b1942 (consBan b1943 (consBan b1944 (consBan b1945 (consBan b1946 (consBan b1947 (consBan b1948 (consBan b1949 (consBan b1950 (consBan b1951 (consBan b1952 (consBan b1953 (consBan b1954 (consBan b1955 (consBan b1956 (consBan b1957 (consBan b1958 (consBan b1959 (consBan b1960 (consBan b1961 (consBan b1962 (consBan b1963 (consBan b1964 (consBan b1965 (consBan b1966 (consBan b1239 (consBan b1317 (consBan b1967 (consBan b1428 (consBan b1503 (consBan b1968 (consBan b1969 (consBan b1970 (consBan b1971 (consBan b1972 (consBan b1973 (consBan b1974 (consBan b1975 (consBan b1976 (consBan b1977 (consBan b1980 (consBan b1981 (consBan b1982 (consBan b1983 (consBan b1984 (consBan b1985 (consBan b1986 (consBan b1987 (consBan b1988 (consBan b1989 (consBan b1990 (consBan b1991 (consBan b1992 (consBan b1993 (consBan b1994 (consBan b1995 (consBan b1996 (consBan b1997 (consBan b2000 (consBan b2001 (consBan b2002 (consBan b2003 (consBan b2004 (consBan b2005 (consBan b2006 (consBan b2007 (consBan b2008 (consBan b2009 (consBan b2010 (consBan b2011 (consBan b2012 (consBan b2013 (consBan b2014 (consBan b2015 (consBan b2048 (consBan b2049 (consBan b2052 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2054:B 89 7 e1885:=viaPerm pt0 pti0 b2053 (by decide +kernel) (by decide +kernel)
theorem b2055:B 89 7 e1886:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2080:B 89 6 e1911:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2081:B 89 6 e1912:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2082:B 89 6 e1913:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2083:B 89 6 e1914:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2084:B 89 6 e1915:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2085:B 89 6 e1916:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2086:B 89 6 e1917:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2087:B 89 6 e1918:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2088:B 89 6 e1919:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2089:B 89 6 e1920:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2090:B 89 6 e1921:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2091:B 89 6 e1922:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2092:B 89 6 e1923:=viaPerm pt0 pti0 b236 (by decide +kernel) (by decide +kernel)
theorem b2093:B 89 6 e1924:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2094:B 89 6 e1925:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2095:B 89 6 e1926:=viaPerm pt0 pti0 b542 (by decide +kernel) (by decide +kernel)
theorem b2096:B 89 6 e1927:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2097:B 89 6 e1928:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2098:B 89 6 e1929:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2099:B 89 6 e1930:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2100:B 89 6 e1931:=viaPerm pt0 pti0 b910 (by decide +kernel) (by decide +kernel)
theorem b2101:B 89 6 e1932:=viaPerm pt0 pti0 b1019 (by decide +kernel) (by decide +kernel)
theorem b2102:B 89 6 e1933:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2103:B 89 6 e1934:=viaPerm pt0 pti0 b1124 (by decide +kernel) (by decide +kernel)
theorem b2104:B 89 6 e1935:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2105:B 89 6 e1936:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2106:B 89 6 e1937:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2107:B 89 6 e1938:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2108:B 89 6 e1939:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2109:B 89 6 e1940:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2110:B 89 6 e1941:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2111:B 89 6 e1942:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2112:B 89 6 e1943:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2113:B 89 6 e1944:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2114:B 89 6 e1884:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2115:B 89 6 e1945:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2116:B 89 6 e1946:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2117:B 89 6 e1947:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2118:B 89 6 e1948:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2119:B 89 6 e1949:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2120:B 89 6 e1950:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2121:B 89 6 e1951:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2122:B 89 6 e1952:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2123:B 89 6 e1953:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2124:B 89 6 e1954:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2125:B 89 6 e1955:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2126:B 89 6 e1956:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2127:B 89 6 e1957:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2128:B 89 6 e1958:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2129:B 89 6 e1959:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2130:B 89 6 e1960:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2131:B 16 3 e1961:=viaSmall (by decide +kernel) (by decide)
theorem w2132:W 16 3 e1961:=widen (by decide +kernel) b2131
theorem b2133:B 89 6 e1962:=viaCut pjt_9 w2132 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2134:B 89 6 e1963:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2135:B 89 6 e1964:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2136:B 89 6 e1965:=viaCut pjt_9 w2132 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2137:B 89 6 e1966:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2138:B 89 6 e1967:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2139:B 89 6 e1968:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2140:B 89 6 e1969:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2141:B 89 6 e1970:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2142:B 89 6 e1971:=viaPerm pt0 pti0 b1704 (by decide +kernel) (by decide +kernel)
theorem b2143:B 89 6 e1972:=viaPerm pt0 pti0 b1622 (by decide +kernel) (by decide +kernel)
theorem b2144:B 89 6 e1973:=viaPerm pt0 pti0 b1706 (by decide +kernel) (by decide +kernel)
theorem b2145:B 89 6 e1974:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2146:B 89 6 e1975:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2147:B 89 6 e1976:=viaPerm pt0 pti0 b1874 (by decide +kernel) (by decide +kernel)
theorem b2148:B 89 6 e1977:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2149:B 89 6 e1978:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2150:B 89 6 e1979:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2151:B 89 6 e1980:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2152:B 89 6 e1981:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2153:B 89 6 e1982:=viaCut pjt_9 w2132 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2154:B 89 6 e1983:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2155:B 89 6 e1984:=viaCut pjt_9 w2132 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2156:B 89 6 e1985:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2157:B 89 7 e1824:=viaBranch (ws:=[e1911,e1912,e1913,e1914,e1915,e1916,e1917,e1918,e1919,e822,e919,e1920,e1012,e1921,e1922,e1923,e1924,e1925,e1926,e1927,e1928,e1929,e1930,e1931,e1932,e1933,e1934,e1935,e1936,e1123,e1199,e1937,e1303,e1370,e1938,e1939,e1940,e1941,e1942,e1943,e1711,e1944,e1884,e1823,e1825,e1945,e1946,e1947,e1948,e1949,e1950,e1951,e1952,e1953,e1954,e1955,e1956,e1957,e1958,e1959,e1960,e1962,e1963,e1964,e1965,e1966,e1967,e1968,e1969,e1970,e1971,e1972,e1973,e1974,e1975,e1976,e1977,e1978,e1979,e1980,e1981,e1982,e1983,e1984,e1985]) (consBan b2080 (consBan b2081 (consBan b2082 (consBan b2083 (consBan b2084 (consBan b2085 (consBan b2086 (consBan b2087 (consBan b2088 (consBan b908 (consBan b1018 (consBan b2089 (consBan b1122 (consBan b2090 (consBan b2091 (consBan b2092 (consBan b2093 (consBan b2094 (consBan b2095 (consBan b2096 (consBan b2097 (consBan b2098 (consBan b2099 (consBan b2100 (consBan b2101 (consBan b2102 (consBan b2103 (consBan b2104 (consBan b2105 (consBan b1242 (consBan b1319 (consBan b2106 (consBan b1431 (consBan b1505 (consBan b2107 (consBan b2108 (consBan b2109 (consBan b2110 (consBan b2111 (consBan b2112 (consBan b1872 (consBan b2113 (consBan b2114 (consBan b1988 (consBan b1990 (consBan b2115 (consBan b2116 (consBan b2117 (consBan b2118 (consBan b2119 (consBan b2120 (consBan b2121 (consBan b2122 (consBan b2123 (consBan b2124 (consBan b2125 (consBan b2126 (consBan b2127 (consBan b2128 (consBan b2129 (consBan b2130 (consBan b2133 (consBan b2134 (consBan b2135 (consBan b2136 (consBan b2137 (consBan b2138 (consBan b2139 (consBan b2140 (consBan b2141 (consBan b2142 (consBan b2143 (consBan b2144 (consBan b2145 (consBan b2146 (consBan b2147 (consBan b2148 (consBan b2149 (consBan b2150 (consBan b2151 (consBan b2152 (consBan b2153 (consBan b2154 (consBan b2155 (consBan b2156 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2158:B 89 7 e1986:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2159:B 89 7 e1987:=viaPerm pt0 pti0 b2157 (by decide +kernel) (by decide +kernel)
theorem b2160:B 89 7 e1988:=viaPerm pt0 pti0 b2158 (by decide +kernel) (by decide +kernel)
theorem b2161:B 89 7 e1989:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2171:B 89 6 e1998:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2172:B 89 6 e1999:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2173:B 89 6 e2000:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2174:B 89 6 e2001:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2175:B 89 6 e2002:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2176:B 89 6 e2003:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2177:B 89 6 e2004:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2178:B 89 6 e2005:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2179:B 89 6 e2006:=viaPerm pt0 pti0 b324 (by decide +kernel) (by decide +kernel)
theorem b2180:B 89 6 e2007:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2181:B 89 6 e2008:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2182:B 89 6 e2009:=viaPerm pt0 pti0 b553 (by decide +kernel) (by decide +kernel)
theorem b2183:B 89 6 e2010:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2184:B 89 6 e2011:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2185:B 89 6 e2012:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2186:B 89 6 e2013:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2187:B 89 6 e2014:=viaPerm pt0 pti0 b925 (by decide +kernel) (by decide +kernel)
theorem b2188:B 89 6 e2015:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2189:B 89 6 e2016:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2190:B 89 6 e2017:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2191:B 89 6 e2018:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2192:B 89 6 e2019:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2193:B 89 6 e2020:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2194:B 89 6 e2021:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2195:B 89 6 e2022:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2196:B 89 6 e2023:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2197:B 89 6 e2024:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2198:B 89 6 e2025:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2199:B 89 6 e2026:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2200:B 89 6 e2027:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2201:B 89 6 e2028:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2202:B 89 6 e2029:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2203:B 6 3 e608:=viaSmall (by decide +kernel) (by decide)
theorem w2204:W 6 3 e608:=widen (by decide +kernel) b2203
theorem b2205:B 89 6 e2030:=viaCut pjt_20 w2204 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2206:B 89 6 e2031:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2207:B 89 6 e2032:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2208:B 89 6 e2033:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2250:B 89 5 e2067:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2251:B 89 5 e2068:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2252:B 89 5 e2069:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2253:B 89 5 e2070:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2254:B 89 5 e2071:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2255:B 20 2 e2072:=viaSmall (by decide +kernel) (by decide)
theorem w2256:W 20 2 e2072:=widen (by decide +kernel) b2255
theorem b2257:B 89 5 e2073:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2258:B 89 5 e2074:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2259:B 89 5 e2075:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2260:B 89 5 e2076:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2261:B 89 5 e2077:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2262:B 89 5 e2078:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2263:B 89 5 e2079:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2264:B 89 5 e2080:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2265:B 89 5 e2081:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2266:B 89 5 e2082:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2267:B 89 5 e2083:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2268:B 89 5 e2084:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2269:B 89 5 e2085:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2270:B 89 5 e2086:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2271:B 89 5 e2087:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2272:B 89 5 e2088:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2273:B 89 5 e2089:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2274:B 89 5 e2090:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2275:B 89 5 e2091:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2276:B 89 5 e2092:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2277:B 89 5 e2093:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2278:B 89 5 e2094:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2279:B 89 5 e2095:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2280:B 89 5 e2096:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2281:B 20 3 e2072:=viaSmall (by decide +kernel) (by decide)
theorem w2282:W 20 3 e2072:=widen (by decide +kernel) b2281
theorem b2283:B 89 5 e2097:=viaCut pjt_11 w2282 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2284:B 89 5 e2098:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2285:B 89 5 e2099:=viaCut pjt_11 w2282 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2286:B 89 5 e2100:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2287:B 89 5 e2101:=viaCut pjt_11 w2282 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2288:B 89 5 e2102:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2289:B 89 5 e2103:=viaCut pjt_11 w2282 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2290:B 89 5 e2104:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2291:B 89 5 e2105:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2292:B 89 5 e2106:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2293:B 89 5 e2107:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2294:B 89 5 e2108:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2295:B 89 5 e2109:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2296:B 89 5 e2110:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2297:B 89 5 e2111:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2298:B 89 5 e2112:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2299:B 89 5 e2113:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2300:B 89 5 e2114:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2301:B 89 5 e2115:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2302:B 89 5 e2116:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2303:B 89 5 e2117:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2304:B 89 6 e2118:=viaBranch (ws:=[e2067,e2068,e2069,e2070,e2071,e2073,e2074,e2075,e2076,e2077,e2078,e2079,e2080,e2081,e2082,e2083,e2084,e2085,e2086,e2087,e2088,e2089,e2090,e2091,e2092,e2093,e2094,e2095,e2096,e2097,e2098,e2099,e2100,e2101,e2102,e2103,e2104,e2105,e2106,e2107,e2108,e2109,e2110,e2111,e2112,e2113,e2114,e2115,e2116,e2117]) (consBan b2250 (consBan b2251 (consBan b2252 (consBan b2253 (consBan b2254 (consBan b2257 (consBan b2258 (consBan b2259 (consBan b2260 (consBan b2261 (consBan b2262 (consBan b2263 (consBan b2264 (consBan b2265 (consBan b2266 (consBan b2267 (consBan b2268 (consBan b2269 (consBan b2270 (consBan b2271 (consBan b2272 (consBan b2273 (consBan b2274 (consBan b2275 (consBan b2276 (consBan b2277 (consBan b2278 (consBan b2279 (consBan b2280 (consBan b2283 (consBan b2284 (consBan b2285 (consBan b2286 (consBan b2287 (consBan b2288 (consBan b2289 (consBan b2290 (consBan b2291 (consBan b2292 (consBan b2293 (consBan b2294 (consBan b2295 (consBan b2296 (consBan b2297 (consBan b2298 (consBan b2299 (consBan b2300 (consBan b2301 (consBan b2302 (consBan b2303 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2306:B 89 5 e2120:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2307:B 89 5 e2121:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2308:B 89 5 e2122:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2309:B 89 5 e2123:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2310:B 89 5 e2124:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2311:B 89 5 e2125:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2312:B 89 5 e2126:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2313:B 89 5 e2127:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2314:B 89 5 e2128:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2315:B 89 5 e2129:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2316:B 89 5 e2130:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2317:B 89 5 e2131:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2318:B 89 5 e2132:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2319:B 89 5 e2133:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2320:B 89 5 e2134:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2321:B 6 2 e655:=viaSmall (by decide +kernel) (by decide)
theorem w2322:W 6 2 e655:=viaSub (ws:=[e83,e655]) (consBan b1051 (consBan b2321 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2323:B 89 5 e2135:=viaCut pjt_27 w2322 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2324:B 89 5 e2136:=viaCut pjt_11 w2256 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2325:B 6 2 e655:=viaSmall (by decide +kernel) (by decide)
theorem w2326:W 6 2 e655:=viaSub (ws:=[e83,e655]) (consBan b433 (consBan b2325 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2327:B 89 5 e2137:=viaCut pjt_20 w2326 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2328:B 89 5 e2138:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2329:B 89 5 e2139:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2330:B 89 5 e2140:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2331:B 89 5 e2141:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2332:B 89 5 e2142:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2333:B 89 5 e2143:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2334:B 89 5 e2144:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2335:B 89 5 e2145:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2336:B 89 5 e2146:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2337:B 89 5 e2147:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2338:B 89 5 e2148:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2339:B 6 2 e608:=viaSmall (by decide +kernel) (by decide)
theorem w2340:W 6 2 e608:=widen (by decide +kernel) b2339
theorem b2341:B 89 5 e2149:=viaCut pjt_20 w2340 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2342:B 89 5 e2150:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2343:B 89 5 e2151:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2344:B 89 6 e2152:=viaBranch (ws:=[e2120,e2121,e2122,e2123,e2124,e2125,e2126,e2127,e2128,e2129,e2130,e2131,e2132,e2133,e2134,e2135,e2136,e2137,e2138,e2139,e2140,e2141,e2142,e2143,e2144,e2145,e2146,e2115,e2147,e2117,e2148,e2149,e2150,e2151]) (consBan b2306 (consBan b2307 (consBan b2308 (consBan b2309 (consBan b2310 (consBan b2311 (consBan b2312 (consBan b2313 (consBan b2314 (consBan b2315 (consBan b2316 (consBan b2317 (consBan b2318 (consBan b2319 (consBan b2320 (consBan b2323 (consBan b2324 (consBan b2327 (consBan b2328 (consBan b2329 (consBan b2330 (consBan b2331 (consBan b2332 (consBan b2333 (consBan b2334 (consBan b2335 (consBan b2336 (consBan b2301 (consBan b2337 (consBan b2303 (consBan b2338 (consBan b2341 (consBan b2342 (consBan b2343 (nilBan _ _))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2345:B 89 6 e2153:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2346:B 89 6 e2154:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2347:B 89 6 e2151:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2348:B 89 6 e2155:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2349:B 89 6 e2156:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2350:B 89 6 e2157:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2351:B 89 6 e2158:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2352:B 89 6 e2159:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2353:B 89 6 e2160:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2354:B 89 6 e2161:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2355:B 89 6 e2162:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2356:B 89 6 e2163:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2357:B 89 6 e2164:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2358:B 89 6 e2165:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2359:B 20 3 e2166:=viaPerm pc11_2 pci11_2 b718 (by decide +kernel) (by decide +kernel)
theorem w2360:W 20 3 e2166:=widen (by decide +kernel) b2359
theorem b2361:B 89 6 e2167:=viaCut pjt_11 w2360 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2362:B 89 6 e2168:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2363:B 89 6 e2169:=viaCut pjt_11 w2360 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2364:B 20 4 e2166:=viaPerm pc11_0 pci11_0 b1719 (by decide +kernel) (by decide +kernel)
theorem w2365:W 20 4 e2166:=widen (by decide +kernel) b2364
theorem b2366:B 89 6 e2170:=viaCut pjt_11 w2365 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2367:B 89 6 e2171:=viaCut pjt_11 w2360 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2368:B 89 6 e2172:=viaCut pjt_11 w2365 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2369:B 89 6 e2173:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2370:B 89 6 e2174:=viaPerm pt0 pti0 b1639 (by decide +kernel) (by decide +kernel)
theorem b2371:B 89 6 e2175:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2372:B 89 6 e2176:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2373:B 89 6 e2177:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2374:B 89 6 e2178:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2375:B 89 6 e2179:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2376:B 89 6 e2180:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2377:B 89 6 e2181:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2378:B 89 6 e2182:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2379:B 89 6 e2183:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2380:B 89 6 e2184:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2381:B 89 6 e2185:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2382:B 89 6 e2186:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2383:B 89 6 e2187:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2384:B 89 6 e2188:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2385:B 89 7 e2189:=viaBranch (ws:=[e1998,e1999,e2000,e2001,e2002,e827,e921,e2003,e1017,e2004,e2005,e2006,e2007,e2008,e2009,e2010,e2011,e2012,e2013,e2014,e2015,e2016,e2017,e2018,e2019,e1128,e1201,e2020,e1308,e1372,e2021,e1563,e2022,e2023,e2024,e2025,e2026,e2027,e2028,e2029,e2030,e2031,e2032,e2033,e2118,e2152,e2153,e2154,e2151,e2155,e2156,e2157,e2158,e2159,e2160,e2161,e2162,e2163,e2164,e2165,e2167,e2168,e2169,e2170,e2171,e2172,e2173,e2174,e2175,e2176,e2177,e2178,e2179,e2180,e2181,e2182,e2183,e2184,e2185,e2186,e2187,e2188]) (consBan b2171 (consBan b2172 (consBan b2173 (consBan b2174 (consBan b2175 (consBan b913 (consBan b1020 (consBan b2176 (consBan b1127 (consBan b2177 (consBan b2178 (consBan b2179 (consBan b2180 (consBan b2181 (consBan b2182 (consBan b2183 (consBan b2184 (consBan b2185 (consBan b2186 (consBan b2187 (consBan b2188 (consBan b2189 (consBan b2190 (consBan b2191 (consBan b2192 (consBan b1247 (consBan b1321 (consBan b2193 (consBan b1436 (consBan b1507 (consBan b2194 (consBan b1709 (consBan b2195 (consBan b2196 (consBan b2197 (consBan b2198 (consBan b2199 (consBan b2200 (consBan b2201 (consBan b2202 (consBan b2205 (consBan b2206 (consBan b2207 (consBan b2208 (consBan b2304 (consBan b2344 (consBan b2345 (consBan b2346 (consBan b2347 (consBan b2348 (consBan b2349 (consBan b2350 (consBan b2351 (consBan b2352 (consBan b2353 (consBan b2354 (consBan b2355 (consBan b2356 (consBan b2357 (consBan b2358 (consBan b2361 (consBan b2362 (consBan b2363 (consBan b2366 (consBan b2367 (consBan b2368 (consBan b2369 (consBan b2370 (consBan b2371 (consBan b2372 (consBan b2373 (consBan b2374 (consBan b2375 (consBan b2376 (consBan b2377 (consBan b2378 (consBan b2379 (consBan b2380 (consBan b2381 (consBan b2382 (consBan b2383 (consBan b2384 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2386:B 89 7 e2190:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2387:B 89 7 e2191:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2415:B 89 6 e2215:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2416:B 89 6 e2216:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2417:B 89 6 e2217:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2418:B 89 6 e2218:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2419:B 89 6 e2219:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2420:B 89 6 e2220:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2421:B 89 6 e2221:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2422:B 89 6 e2222:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2423:B 89 6 e2223:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2424:B 89 6 e2224:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2425:B 89 6 e2225:=viaPerm pt0 pti0 b326 (by decide +kernel) (by decide +kernel)
theorem b2426:B 89 6 e2226:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2427:B 89 6 e2227:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2428:B 89 6 e2228:=viaPerm pt0 pti0 b555 (by decide +kernel) (by decide +kernel)
theorem b2429:B 89 6 e2229:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2430:B 89 6 e2230:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2431:B 89 6 e2231:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2432:B 89 6 e2232:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2433:B 89 6 e2233:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2434:B 89 6 e2234:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2435:B 89 6 e2235:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2436:B 89 6 e2236:=viaPerm pt0 pti0 b1141 (by decide +kernel) (by decide +kernel)
theorem b2437:B 89 6 e2237:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2438:B 89 6 e2238:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2439:B 89 6 e2239:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2440:B 89 6 e2240:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2441:B 89 6 e2241:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2442:B 89 6 e2242:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2443:B 89 6 e2243:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2444:B 89 6 e2244:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2445:B 89 6 e2245:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2446:B 89 6 e2246:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2447:B 89 6 e2247:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2448:B 89 6 e2248:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2449:B 89 6 e2189:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2450:B 89 6 e2249:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2451:B 89 6 e2250:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2452:B 89 6 e2251:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2453:B 89 6 e2252:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2454:B 89 6 e2253:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2455:B 89 6 e2254:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2456:B 89 6 e2255:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2457:B 89 6 e2256:=viaPerm pt0 pti0 b2354 (by decide +kernel) (by decide +kernel)
theorem b2458:B 89 6 e2257:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2459:B 89 6 e2258:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2460:B 89 6 e2259:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2461:B 89 6 e2260:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2462:B 89 6 e2261:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2463:B 89 6 e2262:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2464:B 20 3 e2263:=viaPerm pc11_2 pci11_2 b19 (by decide +kernel) (by decide +kernel)
theorem w2465:W 20 3 e2263:=widen (by decide +kernel) b2464
theorem b2466:B 89 6 e2264:=viaCut pjt_11 w2465 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2467:B 89 6 e2265:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2468:B 89 6 e2266:=viaCut pjt_11 w2465 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2469:B 20 4 e2263:=viaPerm pc11_3 pci11_3 b1418 (by decide +kernel) (by decide +kernel)
theorem w2470:W 20 4 e2263:=widen (by decide +kernel) b2469
theorem b2471:B 89 6 e2267:=viaCut pjt_11 w2470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2472:B 89 6 e2268:=viaCut pjt_11 w2465 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2473:B 89 6 e2269:=viaCut pjt_11 w2470 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2474:B 89 6 e2270:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2475:B 89 6 e2271:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2476:B 89 6 e2272:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2477:B 89 6 e2273:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2478:B 89 6 e2274:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2479:B 89 6 e2275:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2480:B 89 6 e2276:=viaPerm pt0 pti0 b1857 (by decide +kernel) (by decide +kernel)
theorem b2481:B 89 6 e2277:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2482:B 89 6 e2278:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2483:B 89 6 e2279:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2484:B 89 6 e2280:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2485:B 89 6 e2281:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2486:B 89 6 e2282:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2487:B 89 6 e2283:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2488:B 89 6 e2284:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2489:B 89 6 e2285:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2490:B 89 6 e2286:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2491:B 89 6 e2287:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2492:B 89 7 e2031:=viaBranch (ws:=[e2215,e2216,e2217,e2218,e2219,e2220,e2221,e830,e922,e2222,e1020,e2223,e2224,e2225,e2226,e2227,e2228,e2229,e2230,e2231,e2232,e2233,e2234,e2235,e2236,e2237,e2238,e1131,e1202,e2239,e1311,e1373,e2240,e1566,e1568,e2241,e2242,e2243,e2244,e2245,e2246,e1949,e2247,e2248,e2030,e2189,e2032,e2249,e2250,e2251,e2252,e2253,e2254,e2255,e2256,e2257,e2258,e2259,e2260,e2261,e2262,e2264,e2265,e2266,e2267,e2268,e2269,e2270,e2271,e2272,e2273,e2274,e2275,e2276,e2277,e2278,e2279,e2280,e2281,e2282,e2283,e2284,e2285,e2286,e2287]) (consBan b2415 (consBan b2416 (consBan b2417 (consBan b2418 (consBan b2419 (consBan b2420 (consBan b2421 (consBan b916 (consBan b1021 (consBan b2422 (consBan b1130 (consBan b2423 (consBan b2424 (consBan b2425 (consBan b2426 (consBan b2427 (consBan b2428 (consBan b2429 (consBan b2430 (consBan b2431 (consBan b2432 (consBan b2433 (consBan b2434 (consBan b2435 (consBan b2436 (consBan b2437 (consBan b2438 (consBan b1250 (consBan b1322 (consBan b2439 (consBan b1439 (consBan b1508 (consBan b2440 (consBan b1713 (consBan b1717 (consBan b2441 (consBan b2442 (consBan b2443 (consBan b2444 (consBan b2445 (consBan b2446 (consBan b2119 (consBan b2447 (consBan b2448 (consBan b2205 (consBan b2449 (consBan b2207 (consBan b2450 (consBan b2451 (consBan b2452 (consBan b2453 (consBan b2454 (consBan b2455 (consBan b2456 (consBan b2457 (consBan b2458 (consBan b2459 (consBan b2460 (consBan b2461 (consBan b2462 (consBan b2463 (consBan b2466 (consBan b2467 (consBan b2468 (consBan b2471 (consBan b2472 (consBan b2473 (consBan b2474 (consBan b2475 (consBan b2476 (consBan b2477 (consBan b2478 (consBan b2479 (consBan b2480 (consBan b2481 (consBan b2482 (consBan b2483 (consBan b2484 (consBan b2485 (consBan b2486 (consBan b2487 (consBan b2488 (consBan b2489 (consBan b2490 (consBan b2491 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2493:B 89 7 e2288:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2494:B 89 7 e1374:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2500:B 89 6 e2293:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2501:B 89 6 e2294:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2502:B 89 6 e2295:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2503:B 89 6 e2296:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2504:B 89 6 e2297:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2505:B 89 6 e2298:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2506:B 89 6 e2299:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2507:B 89 6 e2300:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2508:B 89 6 e2301:=viaPerm pt0 pti0 b366 (by decide +kernel) (by decide +kernel)
theorem b2509:B 89 6 e2302:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2510:B 89 6 e2303:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2511:B 89 6 e2304:=viaPerm pt0 pti0 b577 (by decide +kernel) (by decide +kernel)
theorem b2512:B 89 6 e2305:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2513:B 89 6 e2306:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2514:B 89 6 e2307:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2515:B 89 6 e2308:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2516:B 89 6 e2309:=viaPerm pt0 pti0 b951 (by decide +kernel) (by decide +kernel)
theorem b2517:B 89 6 e2310:=viaPerm pt0 pti0 b1065 (by decide +kernel) (by decide +kernel)
theorem b2518:B 89 6 e2311:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2519:B 89 6 e2312:=viaPerm pt0 pti0 b1172 (by decide +kernel) (by decide +kernel)
theorem b2520:B 89 6 e2313:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2521:B 89 6 e2314:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2522:B 89 6 e2315:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2523:B 89 6 e2316:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2524:B 89 6 e2317:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2525:B 89 6 e2318:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2526:B 89 6 e2319:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2527:B 89 6 e2320:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2528:B 89 6 e2321:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2529:B 89 6 e2322:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2530:B 89 6 e2323:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2531:B 89 6 e2324:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2532:B 89 6 e2325:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2533:B 89 6 e2326:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2534:B 89 6 e2327:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2535:B 89 6 e2328:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2536:B 89 6 e2329:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2537:B 89 6 e2330:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2538:B 89 6 e2331:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2539:B 6 3 e2332:=viaSmall (by decide +kernel) (by decide)
theorem w2540:W 6 3 e2332:=widen (by decide +kernel) b2539
theorem b2541:B 89 6 e2333:=viaCut pjt_23 w2540 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2542:B 89 6 e2334:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2543:B 89 6 e2335:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2544:B 89 6 e2336:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2545:B 89 6 e2337:=viaPerm pt0 pti0 b2376 (by decide +kernel) (by decide +kernel)
theorem b2546:B 89 6 e2338:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2547:B 89 6 e2339:=viaPerm pt0 pti0 b2483 (by decide +kernel) (by decide +kernel)
theorem b2548:B 89 6 e2340:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2549:B 89 6 e2341:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2550:B 20 3 e935:=viaPerm pc11_0 pci11_0 b2359 (by decide +kernel) (by decide +kernel)
theorem w2551:W 20 3 e935:=widen (by decide +kernel) b2550
theorem b2552:B 89 6 e2342:=viaCut pjt_11 w2551 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2553:B 89 6 e2343:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2554:B 89 6 e2344:=viaCut pjt_11 w2551 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2555:B 89 6 e2345:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2556:B 89 6 e2346:=viaCut pjt_11 w2551 (by decide) (by decide +kernel) (by decide +kernel)
theorem w2557:W 20 4 e935:=widen (by decide +kernel) b1719
theorem b2558:B 89 6 e2347:=viaCut pjt_11 w2557 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2559:B 89 6 e2348:=viaCut pjt_11 w2551 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2560:B 89 6 e2349:=viaCut pjt_11 w2557 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2561:B 89 6 e2350:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2562:B 16 4 e2351:=viaSmall (by decide +kernel) (by decide)
theorem w2563:W 16 4 e2351:=widen (by decide +kernel) b2562
theorem b2564:B 89 6 e2352:=viaCut pjt_8 w2563 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2565:B 89 6 e2353:=viaPerm pt0 pti0 b1667 (by decide +kernel) (by decide +kernel)
theorem b2566:B 89 6 e2354:=viaPerm pt0 pti0 b1768 (by decide +kernel) (by decide +kernel)
theorem b2567:B 89 6 e2355:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2568:B 89 6 e2356:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2569:B 89 6 e2357:=viaPerm pt0 pti0 b1893 (by decide +kernel) (by decide +kernel)
theorem b2570:B 89 6 e2358:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2571:B 89 6 e2359:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2572:B 89 6 e2360:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2573:B 89 6 e2361:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2574:B 89 6 e2362:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2575:B 89 6 e2363:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2576:B 89 6 e2364:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2577:B 89 6 e2365:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2578:B 89 6 e2366:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2579:B 89 6 e2367:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2580:B 89 6 e2368:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2581:B 89 7 e2369:=viaBranch (ws:=[e2293,e2294,e2295,e2296,e2297,e833,e923,e2298,e1023,e2299,e2300,e2301,e2302,e2303,e2304,e2305,e2306,e2307,e2308,e2309,e2310,e2311,e2312,e2313,e2314,e1134,e2315,e2316,e2317,e2318,e2319,e1571,e2320,e2321,e2322,e2323,e2324,e2325,e2326,e2118,e2327,e2153,e2328,e2329,e2330,e2250,e2331,e2333,e2334,e2335,e2336,e2337,e2338,e2339,e2340,e2341,e2342,e2343,e2344,e2345,e2346,e2347,e2348,e2349,e2350,e2352,e2353,e2354,e2355,e2356,e2357,e2358,e2359,e2360,e2361,e2362,e2363,e2364,e2365,e2366,e2367,e2368]) (consBan b2500 (consBan b2501 (consBan b2502 (consBan b2503 (consBan b2504 (consBan b919 (consBan b1022 (consBan b2505 (consBan b1133 (consBan b2506 (consBan b2507 (consBan b2508 (consBan b2509 (consBan b2510 (consBan b2511 (consBan b2512 (consBan b2513 (consBan b2514 (consBan b2515 (consBan b2516 (consBan b2517 (consBan b2518 (consBan b2519 (consBan b2520 (consBan b2521 (consBan b1253 (consBan b2522 (consBan b2523 (consBan b2524 (consBan b2525 (consBan b2526 (consBan b1723 (consBan b2527 (consBan b2528 (consBan b2529 (consBan b2530 (consBan b2531 (consBan b2532 (consBan b2533 (consBan b2304 (consBan b2534 (consBan b2345 (consBan b2535 (consBan b2536 (consBan b2537 (consBan b2451 (consBan b2538 (consBan b2541 (consBan b2542 (consBan b2543 (consBan b2544 (consBan b2545 (consBan b2546 (consBan b2547 (consBan b2548 (consBan b2549 (consBan b2552 (consBan b2553 (consBan b2554 (consBan b2555 (consBan b2556 (consBan b2558 (consBan b2559 (consBan b2560 (consBan b2561 (consBan b2564 (consBan b2565 (consBan b2566 (consBan b2567 (consBan b2568 (consBan b2569 (consBan b2570 (consBan b2571 (consBan b2572 (consBan b2573 (consBan b2574 (consBan b2575 (consBan b2576 (consBan b2577 (consBan b2578 (consBan b2579 (consBan b2580 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2582:B 89 6 e2370:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2583:B 89 6 e2371:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2584:B 89 6 e2372:=viaPerm pt0 pti0 b367 (by decide +kernel) (by decide +kernel)
theorem b2585:B 89 6 e2373:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2586:B 89 6 e2374:=viaPerm pt0 pti0 b578 (by decide +kernel) (by decide +kernel)
theorem b2587:B 89 6 e2375:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2588:B 89 6 e2376:=viaPerm pt0 pti0 b952 (by decide +kernel) (by decide +kernel)
theorem b2589:B 89 6 e2377:=viaPerm pt0 pti0 b1173 (by decide +kernel) (by decide +kernel)
theorem b2590:B 89 6 e2378:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2591:B 89 6 e2379:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2592:B 89 6 e2380:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2593:B 89 6 e2381:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2594:B 89 6 e2382:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2595:B 89 6 e2383:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2596:B 89 6 e2384:=viaPerm pt0 pti0 b2000 (by decide +kernel) (by decide +kernel)
theorem b2597:B 89 6 e2385:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2598:B 89 6 e2386:=viaPerm pt0 pti0 b2001 (by decide +kernel) (by decide +kernel)
theorem b2599:B 89 6 e2387:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2600:B 89 6 e2388:=viaPerm pt0 pti0 b2150 (by decide +kernel) (by decide +kernel)
theorem b2601:B 89 6 e2389:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2602:B 89 6 e2390:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2603:B 89 6 e2391:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2604:B 89 6 e2392:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2605:B 89 6 e2393:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2606:B 89 6 e2394:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2607:B 89 6 e2395:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2608:B 89 6 e2396:=viaPerm pt0 pti0 b2377 (by decide +kernel) (by decide +kernel)
theorem b2609:B 89 6 e2397:=viaPerm pt0 pti0 b2484 (by decide +kernel) (by decide +kernel)
theorem b2610:B 89 6 e2398:=viaCut pjt_11 w2551 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2611:B 89 6 e2399:=viaCut pjt_11 w1721 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2612:B 89 6 e2400:=viaCut pjt_11 w2551 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2613:B 89 6 e2401:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2614:B 89 6 e2402:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2615:B 89 6 e2403:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2616:B 89 6 e2404:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2617:B 89 6 e2405:=viaCut pjt_16 w279 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2618:B 89 6 e2406:=viaPerm pt0 pti0 b1668 (by decide +kernel) (by decide +kernel)
theorem b2619:B 89 6 e2407:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2620:B 89 6 e2408:=viaPerm pt0 pti0 b1894 (by decide +kernel) (by decide +kernel)
theorem b2621:B 89 6 e2409:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2622:B 89 6 e2410:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2623:B 89 6 e2411:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2624:B 89 6 e2412:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2625:B 89 6 e2413:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2626:B 89 6 e2414:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2627:B 89 6 e2415:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2628:B 89 6 e2416:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2629:B 89 6 e2417:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2630:B 89 6 e2418:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2631:B 89 6 e2419:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2632:B 89 6 e2420:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2633:B 89 6 e2421:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2634:B 89 6 e2422:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2635:B 89 6 e2423:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2636:B 89 6 e2424:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2637:B 89 7 e2425:=viaBranch (ws:=[e259,e260,e2370,e493,e2371,e834,e1024,e2372,e2373,e2374,e2375,e2376,e2377,e2378,e1204,e2379,e1378,e2380,e1208,e2381,e2382,e1489,e1570,e1490,e2383,e1720,e2384,e2385,e2386,e2387,e2388,e2152,e2389,e2154,e2390,e2251,e2391,e2392,e2393,e2333,e2394,e2335,e2395,e2396,e2397,e2398,e2399,e2400,e2401,e2402,e1606,e2403,e2404,e2405,e2406,e2407,e2408,e2409,e2410,e2411,e2412,e2413,e2414,e2415,e2416,e2417,e2418,e2419,e2420,e2421,e2422,e2423,e2424,e1376]) (consBan b296 (consBan b297 (consBan b2582 (consBan b549 (consBan b2583 (consBan b920 (consBan b1134 (consBan b2584 (consBan b2585 (consBan b2586 (consBan b2587 (consBan b2588 (consBan b2589 (consBan b2590 (consBan b1324 (consBan b2591 (consBan b1513 (consBan b2592 (consBan b1328 (consBan b2593 (consBan b2594 (consBan b1633 (consBan b1722 (consBan b1634 (consBan b2595 (consBan b1881 (consBan b2596 (consBan b2597 (consBan b2598 (consBan b2599 (consBan b2600 (consBan b2344 (consBan b2601 (consBan b2346 (consBan b2602 (consBan b2452 (consBan b2603 (consBan b2604 (consBan b2605 (consBan b2541 (consBan b2606 (consBan b2543 (consBan b2607 (consBan b2608 (consBan b2609 (consBan b2610 (consBan b2611 (consBan b2612 (consBan b2613 (consBan b2614 (consBan b1759 (consBan b2615 (consBan b2616 (consBan b2617 (consBan b2618 (consBan b2619 (consBan b2620 (consBan b2621 (consBan b2622 (consBan b2623 (consBan b2624 (consBan b2625 (consBan b2626 (consBan b2627 (consBan b2628 (consBan b2629 (consBan b2630 (consBan b2631 (consBan b2632 (consBan b2633 (consBan b2634 (consBan b2635 (consBan b2636 (consBan b1511 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2638:B 89 7 e1376:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2648:B 89 6 e2432:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2649:B 89 6 e2433:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2650:B 89 6 e2434:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2651:B 89 6 e2435:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2652:B 89 6 e2436:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2653:B 89 6 e2437:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2654:B 89 6 e2438:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2655:B 89 6 e2439:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2656:B 89 6 e2440:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2657:B 89 6 e2441:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2658:B 89 6 e2442:=viaPerm pt0 pti0 b369 (by decide +kernel) (by decide +kernel)
theorem b2659:B 89 6 e2443:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2660:B 89 6 e2444:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2661:B 89 6 e2445:=viaPerm pt0 pti0 b580 (by decide +kernel) (by decide +kernel)
theorem b2662:B 89 6 e2446:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2663:B 89 6 e2447:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2664:B 89 6 e2448:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2665:B 89 6 e2449:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2666:B 89 6 e2450:=viaPerm pt0 pti0 b954 (by decide +kernel) (by decide +kernel)
theorem b2667:B 89 6 e2451:=viaPerm pt0 pti0 b1066 (by decide +kernel) (by decide +kernel)
theorem b2668:B 89 6 e2452:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2669:B 89 6 e2453:=viaPerm pt0 pti0 b1175 (by decide +kernel) (by decide +kernel)
theorem b2670:B 89 6 e2454:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2671:B 89 6 e2455:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2672:B 89 6 e2456:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2673:B 89 6 e2457:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2674:B 89 6 e2458:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2675:B 89 6 e2459:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2676:B 89 6 e2460:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2677:B 89 6 e2461:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2678:B 89 6 e2462:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2679:B 89 6 e2463:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2680:B 89 6 e2464:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2681:B 89 6 e2465:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2682:B 89 6 e2466:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2683:B 89 6 e2467:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2684:B 89 6 e2468:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2685:B 89 6 e2469:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2686:B 89 6 e2470:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2687:B 89 6 e2471:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2688:B 89 6 e2472:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2689:B 89 6 e2369:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2690:B 89 6 e2473:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2691:B 89 6 e2474:=viaPerm pt0 pti0 b2379 (by decide +kernel) (by decide +kernel)
theorem b2692:B 89 6 e2475:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2693:B 89 6 e2476:=viaPerm pt0 pti0 b2486 (by decide +kernel) (by decide +kernel)
theorem b2694:B 89 6 e2477:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2695:B 89 6 e2478:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2696:B 89 6 e2479:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2697:B 89 6 e2480:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2698:B 20 3 e2481:=viaPerm pc11_0 pci11_0 b2464 (by decide +kernel) (by decide +kernel)
theorem w2699:W 20 3 e2481:=widen (by decide +kernel) b2698
theorem b2700:B 89 6 e2482:=viaCut pjt_11 w2699 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2701:B 89 6 e2483:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2702:B 89 6 e2484:=viaCut pjt_11 w2699 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2703:B 20 4 e2481:=viaPerm pc11_0 pci11_0 b2469 (by decide +kernel) (by decide +kernel)
theorem w2704:W 20 4 e2481:=widen (by decide +kernel) b2703
theorem b2705:B 89 6 e2485:=viaCut pjt_11 w2704 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2706:B 89 6 e2486:=viaCut pjt_11 w2699 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2707:B 89 6 e2487:=viaCut pjt_11 w2704 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2708:B 89 6 e2488:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2713:B 89 6 e2492:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2714:B 89 6 e2493:=viaPerm pt0 pti0 b1670 (by decide +kernel) (by decide +kernel)
theorem b2715:B 89 6 e2494:=viaPerm pt0 pti0 b1769 (by decide +kernel) (by decide +kernel)
theorem b2716:B 89 6 e2495:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2717:B 89 6 e2496:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2718:B 89 6 e2497:=viaPerm pt0 pti0 b1896 (by decide +kernel) (by decide +kernel)
theorem b2719:B 89 6 e2498:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2720:B 89 6 e2499:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2721:B 89 6 e2500:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2722:B 89 6 e2501:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2723:B 89 6 e2502:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2724:B 89 6 e2503:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2725:B 89 6 e2504:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2726:B 89 6 e2505:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2727:B 89 6 e2506:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2728:B 89 6 e2507:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2729:B 89 6 e2508:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2730:B 89 7 e2334:=viaBranch (ws:=[e2432,e2433,e2434,e2435,e2436,e2437,e2438,e836,e924,e2439,e1026,e2440,e2441,e2442,e2443,e2444,e2445,e2446,e2447,e2448,e2449,e2450,e2451,e2452,e2453,e2454,e2455,e2456,e2457,e2458,e1317,e2459,e2460,e1574,e1576,e2461,e2462,e2463,e2464,e2465,e2466,e1955,e2467,e2468,e2469,e2156,e2470,e2471,e2253,e2472,e2333,e2369,e2335,e2473,e2474,e2475,e2476,e2477,e2478,e2479,e2480,e2482,e2483,e2484,e2485,e2486,e2487,e2488,e2492,e2493,e2494,e2495,e2496,e2497,e2498,e2499,e2500,e2501,e2502,e2503,e2504,e2505,e2506,e2507,e2508]) (consBan b2648 (consBan b2649 (consBan b2650 (consBan b2651 (consBan b2652 (consBan b2653 (consBan b2654 (consBan b922 (consBan b1023 (consBan b2655 (consBan b1136 (consBan b2656 (consBan b2657 (consBan b2658 (consBan b2659 (consBan b2660 (consBan b2661 (consBan b2662 (consBan b2663 (consBan b2664 (consBan b2665 (consBan b2666 (consBan b2667 (consBan b2668 (consBan b2669 (consBan b2670 (consBan b2671 (consBan b2672 (consBan b2673 (consBan b2674 (consBan b1445 (consBan b2675 (consBan b2676 (consBan b1727 (consBan b1729 (consBan b2677 (consBan b2678 (consBan b2679 (consBan b2680 (consBan b2681 (consBan b2682 (consBan b2125 (consBan b2683 (consBan b2684 (consBan b2685 (consBan b2349 (consBan b2686 (consBan b2687 (consBan b2454 (consBan b2688 (consBan b2541 (consBan b2689 (consBan b2543 (consBan b2690 (consBan b2691 (consBan b2692 (consBan b2693 (consBan b2694 (consBan b2695 (consBan b2696 (consBan b2697 (consBan b2700 (consBan b2701 (consBan b2702 (consBan b2705 (consBan b2706 (consBan b2707 (consBan b2708 (consBan b2713 (consBan b2714 (consBan b2715 (consBan b2716 (consBan b2717 (consBan b2718 (consBan b2719 (consBan b2720 (consBan b2721 (consBan b2722 (consBan b2723 (consBan b2724 (consBan b2725 (consBan b2726 (consBan b2727 (consBan b2728 (consBan b2729 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2731:B 89 6 e2509:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2732:B 89 6 e2510:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2733:B 89 6 e2511:=viaPerm pt0 pti0 b370 (by decide +kernel) (by decide +kernel)
theorem b2734:B 89 6 e2512:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2735:B 89 6 e2513:=viaPerm pt0 pti0 b581 (by decide +kernel) (by decide +kernel)
theorem b2736:B 89 6 e2514:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2737:B 89 6 e2515:=viaPerm pt0 pti0 b955 (by decide +kernel) (by decide +kernel)
theorem b2738:B 89 6 e2516:=viaPerm pt0 pti0 b1176 (by decide +kernel) (by decide +kernel)
theorem b2739:B 89 6 e2517:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2740:B 89 6 e2518:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2741:B 89 6 e2519:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2742:B 89 6 e2520:=viaPerm pt0 pti0 b2004 (by decide +kernel) (by decide +kernel)
theorem b2743:B 89 6 e2521:=viaPerm pt0 pti0 b2152 (by decide +kernel) (by decide +kernel)
theorem b2744:B 89 6 e2522:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2745:B 16 3 e2523:=viaSmall (by decide +kernel) (by decide)
theorem w2746:W 16 3 e2523:=widen (by decide +kernel) b2745
theorem b2747:B 89 6 e2524:=viaCut pjt_9 w2746 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2748:B 89 6 e2425:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2749:B 89 6 e2525:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2750:B 89 6 e2526:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2751:B 89 6 e2527:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2752:B 89 6 e2528:=viaPerm pt0 pti0 b2380 (by decide +kernel) (by decide +kernel)
theorem b2753:B 89 6 e2529:=viaPerm pt0 pti0 b2487 (by decide +kernel) (by decide +kernel)
theorem b2754:B 20 4 e2530:=viaPerm pc11_2 pci11_2 b1522 (by decide +kernel) (by decide +kernel)
theorem w2755:W 20 4 e2530:=viaSub (ws:=[e2481,e126,e2530]) (consBan b2703 (consBan b868 (consBan b2754 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2756:B 89 6 e2531:=viaCut pjt_11 w2755 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2757:B 89 6 e2532:=viaCut pjt_11 w2755 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2758:B 89 6 e2533:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2759:B 89 6 e2534:=viaCut pjt_16 w279 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2760:B 89 6 e2535:=viaPerm pt0 pti0 b1671 (by decide +kernel) (by decide +kernel)
theorem b2761:B 89 6 e2536:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2762:B 89 6 e2537:=viaPerm pt0 pti0 b1897 (by decide +kernel) (by decide +kernel)
theorem b2763:B 89 6 e2538:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2764:B 89 6 e2539:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2765:B 89 6 e2540:=viaPerm pt0 pti0 b2624 (by decide +kernel) (by decide +kernel)
theorem b2766:B 89 6 e2541:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2767:B 89 6 e2542:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2768:B 89 6 e2543:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2769:B 89 6 e2544:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2770:B 89 6 e2545:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2771:B 89 7 e2395:=viaBranch (ws:=[e262,e2509,e495,e2510,e837,e1027,e2511,e2512,e2513,e2514,e2515,e2516,e1082,e2517,e1240,e1377,e2455,e1206,e2458,e1379,e1575,e1493,e2518,e1722,e2519,e2520,e1956,e2521,e2522,e2157,e2524,e2254,e2394,e2425,e2525,e2333,e2335,e2526,e2527,e2528,e2529,e1382,e2531,e1385,e1608,e2484,e2532,e2486,e2533,e2534,e2535,e2536,e2537,e1393,e2538,e1395,e2539,e2499,e2540,e2502,e2541,e1399,e2542,e1401,e2543,e2505,e2544,e2507,e2545,e1374]) (consBan b300 (consBan b2731 (consBan b551 (consBan b2732 (consBan b923 (consBan b1137 (consBan b2733 (consBan b2734 (consBan b2735 (consBan b2736 (consBan b2737 (consBan b2738 (consBan b1542 (consBan b2739 (consBan b1360 (consBan b1512 (consBan b2671 (consBan b1326 (consBan b2674 (consBan b1514 (consBan b1728 (consBan b1637 (consBan b2740 (consBan b1883 (consBan b2741 (consBan b2742 (consBan b2126 (consBan b2743 (consBan b2744 (consBan b2350 (consBan b2747 (consBan b2455 (consBan b2606 (consBan b2748 (consBan b2749 (consBan b2541 (consBan b2543 (consBan b2750 (consBan b2751 (consBan b2752 (consBan b2753 (consBan b1517 (consBan b2756 (consBan b1521 (consBan b1761 (consBan b2702 (consBan b2757 (consBan b2706 (consBan b2758 (consBan b2759 (consBan b2760 (consBan b2761 (consBan b2762 (consBan b1530 (consBan b2763 (consBan b1532 (consBan b2764 (consBan b2720 (consBan b2765 (consBan b2723 (consBan b2766 (consBan b1536 (consBan b2767 (consBan b1538 (consBan b2768 (consBan b2726 (consBan b2769 (consBan b2728 (consBan b2770 (consBan b1509 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2772:B 89 7 e2546:=viaPerm pt0 pti0 b2161 (by decide +kernel) (by decide +kernel)
theorem b2773:B 89 7 e2547:=viaPerm pt0 pti0 b2385 (by decide +kernel) (by decide +kernel)
theorem b2774:B 89 7 e2548:=viaPerm pt0 pti0 b2386 (by decide +kernel) (by decide +kernel)
theorem b2775:B 89 7 e2549:=viaPerm pt0 pti0 b2492 (by decide +kernel) (by decide +kernel)
theorem b2776:B 89 7 e2550:=viaPerm pt0 pti0 b2493 (by decide +kernel) (by decide +kernel)
theorem b2777:B 89 7 e2551:=viaPerm pt0 pti0 b2387 (by decide +kernel) (by decide +kernel)
theorem b2778:B 89 7 e2552:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem w2779:W 20 4 e23:=viaSub (ws:=[e299,e22,e23]) (consBan b341 (consBan b37 (consBan b38 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2780:B 89 6 e2553:=viaCut pjt_7 w2779 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2781:B 20 4 e27:=viaPerm pc11_2 pci11_2 b16 (by decide +kernel) (by decide +kernel)
theorem w2782:W 20 4 e27:=widen (by decide +kernel) b2781
theorem b2783:B 89 6 e2554:=viaCut pjt_11 w2782 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2784:B 89 6 e2555:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2785:B 89 6 e2556:=viaPerm pt0 pti0 b330 (by decide +kernel) (by decide +kernel)
theorem b2786:B 89 6 e2557:=viaPerm pt0 pti0 b2780 (by decide +kernel) (by decide +kernel)
theorem b2787:B 89 6 e2558:=viaPerm pt0 pti0 b559 (by decide +kernel) (by decide +kernel)
theorem b2788:B 89 6 e2559:=viaPerm pt0 pti0 b2783 (by decide +kernel) (by decide +kernel)
theorem b2789:B 89 6 e2560:=viaPerm pt0 pti0 b1030 (by decide +kernel) (by decide +kernel)
theorem b2790:B 89 6 e2561:=viaPerm pt0 pti0 b2784 (by decide +kernel) (by decide +kernel)
theorem b2791:B 89 6 e2562:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2792:B 89 6 e2563:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2793:B 20 4 e2564:=viaSmall (by decide +kernel) (by decide)
theorem w2794:W 20 4 e2564:=viaSub (ws:=[e12,e126,e2564]) (consBan b1146 (consBan b147 (consBan b2793 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2795:B 89 6 e2565:=viaCut pjt_15 w2794 (by decide) (by decide +kernel) (by decide +kernel)
theorem w2796:W 35 5 e1411:=widen (by decide +kernel) b1552
theorem b2797:B 89 6 e2566:=viaCut pjt_0 w2796 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2798:B 89 6 e2567:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2805:B 89 6 e2571:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2806:B 89 6 e2572:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2807:B 89 6 e2573:=viaPerm pt0 pti0 b1981 (by decide +kernel) (by decide +kernel)
theorem b2808:B 89 6 e2574:=viaPerm pt0 pti0 b2134 (by decide +kernel) (by decide +kernel)
theorem b2809:B 89 6 e2575:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2810:B 89 6 e2576:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2811:B 89 6 e2577:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2812:B 89 6 e2578:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2813:B 89 6 e2579:=viaCut pjt_15 w148 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2814:B 89 6 e2580:=viaPerm pt0 pti0 b2809 (by decide +kernel) (by decide +kernel)
theorem b2815:B 89 6 e2581:=viaPerm pt0 pti0 b2810 (by decide +kernel) (by decide +kernel)
theorem b2816:B 89 6 e2582:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2817:B 89 6 e2583:=viaPerm pt0 pti0 b2816 (by decide +kernel) (by decide +kernel)
theorem b2818:B 89 6 e2584:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2819:B 89 6 e2585:=viaPerm pt0 pti0 b2818 (by decide +kernel) (by decide +kernel)
theorem b2820:B 89 6 e2586:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2831:B 35 5 e2587:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2832:B 35 5 e2588:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2833:B 35 5 e2589:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2834:B 35 5 e2590:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2835:B 35 5 e2591:=viaSmall (by decide +kernel) (by decide)
theorem w2836:W 35 5 e2591:=viaSub (ws:=[e435,e2587,e2588,e2589,e2590,e2591]) (consBan b486 (consBan b2831 (consBan b2832 (consBan b2833 (consBan b2834 (consBan b2835 (nilBan _ _))))))) (by decide) (by decide +kernel)
theorem b2837:B 89 6 e2592:=viaCut pjt_0 w2836 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2838:B 89 6 e2593:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2839:B 89 6 e2594:=viaPerm pt0 pti0 b2797 (by decide +kernel) (by decide +kernel)
theorem b2840:B 89 6 e2595:=viaPerm pt0 pti0 b2798 (by decide +kernel) (by decide +kernel)
theorem b2841:B 89 6 e2596:=viaPerm pt0 pti0 b1736 (by decide +kernel) (by decide +kernel)
theorem b2842:B 89 6 e2597:=viaPerm pt0 pti0 b2805 (by decide +kernel) (by decide +kernel)
theorem b2843:B 89 6 e2598:=viaPerm pt0 pti0 b2806 (by decide +kernel) (by decide +kernel)
theorem b2844:B 89 6 e2599:=viaPerm pt0 pti0 b2811 (by decide +kernel) (by decide +kernel)
theorem b2845:B 89 6 e2600:=viaPerm pt0 pti0 b1755 (by decide +kernel) (by decide +kernel)
theorem b2846:B 89 6 e2601:=viaPerm pt0 pti0 b2812 (by decide +kernel) (by decide +kernel)
theorem b2847:B 89 6 e2602:=viaPerm pt0 pti0 b2813 (by decide +kernel) (by decide +kernel)
theorem b2848:B 89 6 e2603:=viaPerm pt0 pti0 b2553 (by decide +kernel) (by decide +kernel)
theorem b2849:B 89 6 e2604:=viaPerm pt0 pti0 b2697 (by decide +kernel) (by decide +kernel)
theorem b2850:B 89 6 e2605:=viaPerm pt0 pti0 b2820 (by decide +kernel) (by decide +kernel)
theorem b2851:B 89 6 e2606:=viaPerm pt0 pti0 b2837 (by decide +kernel) (by decide +kernel)
theorem b2852:B 89 6 e2607:=viaPerm pt0 pti0 b2838 (by decide +kernel) (by decide +kernel)
theorem w2853:W 6 2 e83:=widen (by decide +kernel) b334
theorem b2854:B 89 6 e2608:=viaCut pjt_29 w2853 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2855:B 89 6 e2609:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2856:B 6 1 e83:=viaSmall (by decide +kernel) (by decide)
theorem w2857:W 6 1 e83:=widen (by decide +kernel) b2856
theorem b2858:B 89 6 e2610:=viaCut pjt_23 w2857 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2859:B 12 3 e2611:=viaSmall (by decide +kernel) (by decide)
theorem w2860:W 12 3 e2611:=viaSub (ws:=[e16,e2611]) (consBan b30 (consBan b2859 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2861:B 89 6 e2612:=viaCut pjt_18 w2860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2862:B 89 6 e2613:=viaCut pjt_29 w2853 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2863:B 12 3 e2614:=viaSmall (by decide +kernel) (by decide)
theorem b2864:B 12 3 e2615:=viaSmall (by decide +kernel) (by decide)
theorem w2865:W 12 3 e2615:=viaSub (ws:=[e2614,e16,e2615]) (consBan b2863 (consBan b30 (consBan b2864 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2866:B 89 6 e2616:=viaCut pjt_18 w2865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2867:B 6 1 e83:=viaSmall (by decide +kernel) (by decide)
theorem w2868:W 6 1 e83:=widen (by decide +kernel) b2867
theorem b2869:B 89 6 e2617:=viaCut pjt_29 w2868 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2870:B 89 6 e2618:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2871:B 89 7 e2619:=viaBranch (ws:=[e292,e2553,e503,e2554,e931,e2555,e2556,e2557,e2558,e2559,e2560,e2561,e2562,e945,e2563,e2565,e1146,e1326,e2566,e2567,e1583,e2571,e2572,e1816,e2573,e1963,e2574,e2575,e2576,e2577,e1602,e2578,e2579,e2343,e2480,e2580,e2581,e2582,e2583,e2584,e2585,e2586,e2592,e2593,e2594,e2595,e2596,e2597,e2598,e2599,e2600,e2601,e2602,e2603,e2604,e2605,e2606,e2607,e2608,e2609,e2610,e2612,e2613,e2616,e2617,e2618]) (consBan b330 (consBan b2780 (consBan b559 (consBan b2783 (consBan b1030 (consBan b2784 (consBan b2785 (consBan b2786 (consBan b2787 (consBan b2788 (consBan b2789 (consBan b2790 (consBan b2791 (consBan b1047 (consBan b2792 (consBan b2795 (consBan b1265 (consBan b1457 (consBan b2797 (consBan b2798 (consBan b1736 (consBan b2805 (consBan b2806 (consBan b1981 (consBan b2807 (consBan b2134 (consBan b2808 (consBan b2809 (consBan b2810 (consBan b2811 (consBan b1755 (consBan b2812 (consBan b2813 (consBan b2553 (consBan b2697 (consBan b2814 (consBan b2815 (consBan b2816 (consBan b2817 (consBan b2818 (consBan b2819 (consBan b2820 (consBan b2837 (consBan b2838 (consBan b2839 (consBan b2840 (consBan b2841 (consBan b2842 (consBan b2843 (consBan b2844 (consBan b2845 (consBan b2846 (consBan b2847 (consBan b2848 (consBan b2849 (consBan b2850 (consBan b2851 (consBan b2852 (consBan b2854 (consBan b2855 (consBan b2858 (consBan b2861 (consBan b2862 (consBan b2866 (consBan b2869 (consBan b2870 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2872:B 89 7 e2605:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2873:B 89 7 e2586:=viaPerm pt0 pti0 b2872 (by decide +kernel) (by decide +kernel)
theorem b2874:B 89 7 e1382:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2875:B 89 6 e2620:=viaCut pjt_6 w1037 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2876:B 89 6 e2621:=viaCut pjt_11 w2782 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2877:B 89 6 e2622:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2878:B 89 6 e2623:=viaPerm pt0 pti0 b372 (by decide +kernel) (by decide +kernel)
theorem b2880:B 89 6 e2625:=viaCut pjt_6 w1037 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2881:B 89 6 e2626:=viaPerm pt0 pti0 b583 (by decide +kernel) (by decide +kernel)
theorem b2887:B 89 6 e2632:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2888:B 89 6 e2633:=viaPerm pt0 pti0 b957 (by decide +kernel) (by decide +kernel)
theorem b2889:B 89 6 e2634:=viaPerm pt0 pti0 b1178 (by decide +kernel) (by decide +kernel)
theorem b2890:B 89 6 e2635:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2891:B 89 6 e2636:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2892:B 20 4 e2637:=viaSmall (by decide +kernel) (by decide)
theorem b2893:B 20 4 e2638:=viaSmall (by decide +kernel) (by decide)
theorem w2894:W 20 4 e2638:=viaSub (ws:=[e126,e2637,e2638]) (consBan b147 (consBan b2892 (consBan b2893 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2895:B 89 6 e2639:=viaCut pjt_15 w2894 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2896:B 40 5 e2640:=viaPerm pc1_1 pci1_1 b394 (by decide +kernel) (by decide +kernel)
theorem w2897:W 40 5 e2640:=widen (by decide +kernel) b2896
theorem b2898:B 89 6 e2641:=viaCut pjt_1 w2897 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2899:B 89 6 e2642:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2903:B 89 6 e2643:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2904:B 89 6 e2644:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2905:B 89 6 e2645:=viaPerm pt0 pti0 b2048 (by decide +kernel) (by decide +kernel)
theorem b2906:B 89 6 e2646:=viaPerm pt0 pti0 b2154 (by decide +kernel) (by decide +kernel)
theorem b2907:B 89 6 e2647:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2908:B 89 6 e2648:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2909:B 89 6 e2649:=viaCut pjt_11 w2755 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2910:B 89 6 e2650:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2911:B 89 6 e2651:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2912:B 89 6 e2652:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2913:B 20 4 e2653:=viaSmall (by decide +kernel) (by decide)
theorem w2914:W 20 4 e2653:=widen (by decide +kernel) b2913
theorem b2915:B 89 6 e2654:=viaCut pjt_6 w2914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2916:B 89 6 e2655:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2917:B 89 6 e2656:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2918:B 89 6 e2657:=viaCut pjt_16 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2919:B 89 6 e2658:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2924:B 40 5 e2663:=viaSmall (by decide +kernel) (by decide)
theorem b2925:B 40 5 e2664:=viaSmall (by decide +kernel) (by decide)
theorem w2926:W 40 5 e2664:=viaSub (ws:=[e2663,e2664]) (consBan b2924 (consBan b2925 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2927:B 89 6 e2665:=viaCut pjt_2 w2926 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2928:B 89 6 e2666:=viaPerm pt0 pti0 b1673 (by decide +kernel) (by decide +kernel)
theorem b2939:B 89 6 e2674:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2940:B 89 6 e2675:=viaPerm pt0 pti0 b1899 (by decide +kernel) (by decide +kernel)
theorem b2941:B 89 6 e2676:=viaPerm pt0 pti0 b2630 (by decide +kernel) (by decide +kernel)
theorem b2942:B 89 6 e2677:=viaPerm pt0 pti0 b2769 (by decide +kernel) (by decide +kernel)
theorem b2943:B 89 6 e2678:=viaCut pjt_18 w31 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2944:B 16 4 e2679:=viaSmall (by decide +kernel) (by decide)
theorem w2945:W 16 4 e2679:=widen (by decide +kernel) b2944
theorem b2946:B 89 6 e2680:=viaCut pjt_16 w2945 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2947:B 89 6 e2681:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2948:B 89 6 e2682:=viaPerm pt0 pti0 b2634 (by decide +kernel) (by decide +kernel)
theorem b2949:B 89 6 e2683:=viaCut pjt_18 w94 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2950:B 16 4 e2684:=viaSmall (by decide +kernel) (by decide)
theorem w2951:W 16 4 e2684:=widen (by decide +kernel) b2950
theorem b2952:B 89 6 e2685:=viaCut pjt_16 w2951 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2953:B 89 6 e2686:=viaCut pjt_16 w2951 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2954:B 89 6 e2687:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2963:B 40 5 e2694:=viaPerm pc2_2 pci2_2 b49 (by decide +kernel) (by decide +kernel)
theorem b2964:B 40 5 e2695:=viaSmall (by decide +kernel) (by decide)
theorem w2965:W 40 5 e2695:=viaSub (ws:=[e2694,e2695]) (consBan b2963 (consBan b2964 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2966:B 89 6 e2696:=viaCut pjt_2 w2965 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2967:B 20 4 e2697:=viaSmall (by decide +kernel) (by decide)
theorem b2968:B 20 4 e2698:=viaSmall (by decide +kernel) (by decide)
theorem w2969:W 20 4 e2698:=viaSub (ws:=[e126,e2697,e2698]) (consBan b868 (consBan b2967 (consBan b2968 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2970:B 89 6 e2699:=viaCut pjt_11 w2969 (by decide) (by decide +kernel) (by decide +kernel)
theorem w2971:W 6 2 e83:=widen (by decide +kernel) b1051
theorem b2972:B 89 6 e2700:=viaCut pjt_27 w2971 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2973:B 6 1 e83:=viaSmall (by decide +kernel) (by decide)
theorem w2974:W 6 1 e83:=widen (by decide +kernel) b2973
theorem b2975:B 89 6 e2701:=viaCut pjt_27 w2974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2976:B 89 6 e2702:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2977:B 89 6 e2703:=viaCut pjt_15 w163 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2978:B 89 6 e2704:=viaCut pjt_27 w2971 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2979:B 89 6 e2705:=viaCut pjt_27 w2974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2980:B 12 3 e2706:=viaPerm pc18_0 pci18_0 b2863 (by decide +kernel) (by decide +kernel)
theorem b2981:B 12 3 e2707:=viaPerm pc18_0 pci18_0 b2864 (by decide +kernel) (by decide +kernel)
theorem w2982:W 12 3 e2707:=viaSub (ws:=[e16,e2706,e2707]) (consBan b30 (consBan b2980 (consBan b2981 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b2983:B 89 6 e2708:=viaCut pjt_18 w2982 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2984:B 89 7 e2709:=viaBranch (ws:=[e307,e2620,e507,e2621,e937,e2622,e2623,e2625,e2626,e2632,e2633,e2634,e1214,e1387,e2635,e950,e2636,e2639,e2641,e2642,e1594,e2643,e2644,e1820,e2645,e1967,e2646,e2170,e2267,e2399,e2532,e2647,e1606,e2648,e2649,e2650,e2651,e2592,e2652,e2654,e2655,e2656,e2657,e2658,e2665,e2666,e2674,e2675,e2676,e2677,e2678,e2680,e2681,e2682,e2683,e2685,e2686,e2687,e2696,e2699,e2700,e2701,e2702,e2612,e2703,e2704,e2705,e2708,e1385]) (consBan b350 (consBan b2875 (consBan b565 (consBan b2876 (consBan b1038 (consBan b2877 (consBan b2878 (consBan b2880 (consBan b2881 (consBan b2887 (consBan b2888 (consBan b2889 (consBan b1334 (consBan b1524 (consBan b2890 (consBan b1056 (consBan b2891 (consBan b2895 (consBan b2898 (consBan b2899 (consBan b1747 (consBan b2903 (consBan b2904 (consBan b1985 (consBan b2905 (consBan b2138 (consBan b2906 (consBan b2366 (consBan b2471 (consBan b2611 (consBan b2757 (consBan b2907 (consBan b1759 (consBan b2908 (consBan b2909 (consBan b2910 (consBan b2911 (consBan b2837 (consBan b2912 (consBan b2915 (consBan b2916 (consBan b2917 (consBan b2918 (consBan b2919 (consBan b2927 (consBan b2928 (consBan b2939 (consBan b2940 (consBan b2941 (consBan b2942 (consBan b2943 (consBan b2946 (consBan b2947 (consBan b2948 (consBan b2949 (consBan b2952 (consBan b2953 (consBan b2954 (consBan b2966 (consBan b2970 (consBan b2972 (consBan b2975 (consBan b2976 (consBan b2861 (consBan b2977 (consBan b2978 (consBan b2979 (consBan b2983 (consBan b1521 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2985:B 89 7 e1385:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2993:B 16 3 e1814:=viaPerm pc13_0 pci13_0 b1497 (by decide +kernel) (by decide +kernel)
theorem w2994:W 16 3 e1814:=widen (by decide +kernel) b2993
theorem b2995:B 89 6 e2714:=viaCut pjt_13 w2994 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2996:B 16 3 e1961:=viaSmall (by decide +kernel) (by decide)
theorem w2997:W 16 3 e1961:=widen (by decide +kernel) b2996
theorem b2998:B 89 6 e2715:=viaCut pjt_13 w2997 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2999:B 89 6 e2716:=viaPerm pt0 pti0 b374 (by decide +kernel) (by decide +kernel)
theorem b3000:B 16 3 e2717:=viaPerm pc16_0 pci16_0 b278 (by decide +kernel) (by decide +kernel)
theorem w3001:W 16 3 e2717:=widen (by decide +kernel) b3000
theorem b3002:B 89 6 e2718:=viaCut pjt_16 w3001 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3003:B 89 6 e2719:=viaPerm pt0 pti0 b585 (by decide +kernel) (by decide +kernel)
theorem b3004:B 16 3 e2720:=viaSmall (by decide +kernel) (by decide)
theorem w3005:W 16 3 e2720:=widen (by decide +kernel) b3004
theorem b3006:B 89 6 e2721:=viaCut pjt_16 w3005 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3007:B 89 6 e2722:=viaPerm pt0 pti0 b959 (by decide +kernel) (by decide +kernel)
theorem b3008:B 89 6 e2723:=viaPerm pt0 pti0 b1180 (by decide +kernel) (by decide +kernel)
theorem b3009:B 89 6 e2724:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3010:B 89 6 e2725:=viaCut pjt_13 w1498 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3011:B 16 3 e2726:=viaPerm pc13_0 pci13_0 b2996 (by decide +kernel) (by decide +kernel)
theorem w3012:W 16 3 e2726:=widen (by decide +kernel) b3011
theorem b3013:B 89 6 e2727:=viaCut pjt_13 w3012 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3014:B 89 6 e2728:=viaPerm pt0 pti0 b2052 (by decide +kernel) (by decide +kernel)
theorem b3015:B 89 6 e2729:=viaPerm pt0 pti0 b2156 (by decide +kernel) (by decide +kernel)
theorem b3016:B 89 6 e2730:=viaCut pjt_18 w355 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3017:B 89 6 e2731:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3018:B 89 6 e2732:=viaPerm pt0 pti0 b2491 (by decide +kernel) (by decide +kernel)
theorem b3019:B 6 1 e83:=viaSmall (by decide +kernel) (by decide)
theorem w3020:W 6 1 e83:=widen (by decide +kernel) b3019
theorem b3021:B 89 6 e2733:=viaCut pjt_31 w3020 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3022:B 89 6 e2734:=viaCut pjt_31 w3020 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3023:B 89 6 e2709:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3024:B 89 6 e2735:=viaCut pjt_11 w974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3025:B 12 3 e2736:=viaSmall (by decide +kernel) (by decide)
theorem w3026:W 12 3 e2736:=widen (by decide +kernel) b3025
theorem b3027:B 89 6 e2737:=viaCut pjt_18 w3026 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3028:B 12 3 e2738:=viaPerm pc18_4 pci18_4 b3025 (by decide +kernel) (by decide +kernel)
theorem w3029:W 12 3 e2738:=widen (by decide +kernel) b3028
theorem b3030:B 89 6 e2739:=viaCut pjt_18 w3029 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3031:B 89 6 e2740:=viaCut pjt_16 w279 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3032:B 89 6 e2741:=viaPerm pt0 pti0 b1675 (by decide +kernel) (by decide +kernel)
theorem b3033:B 16 3 e2742:=viaPerm pc16_0 pci16_0 b3004 (by decide +kernel) (by decide +kernel)
theorem w3034:W 16 3 e2742:=widen (by decide +kernel) b3033
theorem b3035:B 89 6 e2743:=viaCut pjt_16 w3034 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3036:B 89 6 e2744:=viaPerm pt0 pti0 b1901 (by decide +kernel) (by decide +kernel)
theorem b3037:B 89 6 e2745:=viaCut pjt_11 w869 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3038:B 89 6 e2746:=viaPerm pt0 pti0 b2768 (by decide +kernel) (by decide +kernel)
theorem b3039:B 89 6 e2747:=viaPerm pt0 pti0 b2632 (by decide +kernel) (by decide +kernel)
theorem b3040:B 89 6 e2748:=viaPerm pt0 pti0 b2770 (by decide +kernel) (by decide +kernel)
theorem b3041:B 12 3 e2749:=viaSmall (by decide +kernel) (by decide)
theorem w3042:W 12 3 e2749:=viaSub (ws:=[e16,e2749]) (consBan b30 (consBan b3041 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b3043:B 89 6 e2750:=viaCut pjt_18 w3042 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3044:B 89 6 e2751:=viaPerm pt0 pti0 b2970 (by decide +kernel) (by decide +kernel)
theorem b3045:B 12 3 e2752:=viaSmall (by decide +kernel) (by decide)
theorem w3046:W 12 3 e2752:=widen (by decide +kernel) b3045
theorem b3047:B 89 6 e2753:=viaCut pjt_18 w3046 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3048:B 89 7 e2658:=viaBranch (ws:=[e311,e2714,e509,e2715,e939,e1041,e2716,e2718,e2719,e2721,e2722,e2723,e1082,e2724,e1240,e952,e1216,e1388,e2725,e1596,e2727,e1706,e1822,e2728,e1969,e2729,e2172,e2269,e1374,e2730,e1376,e1608,e2401,e2533,e2731,e2732,e2733,e2734,e2657,e2709,e2735,e2737,e2739,e2740,e2741,e2743,e2744,e1393,e2745,e1395,e2746,e2747,e2748,e1399,e2750,e1401,e2618,e2751,e2753,e1382]) (consBan b356 (consBan b2995 (consBan b567 (consBan b2998 (consBan b1040 (consBan b1154 (consBan b2999 (consBan b3002 (consBan b3003 (consBan b3006 (consBan b3007 (consBan b3008 (consBan b1542 (consBan b3009 (consBan b1360 (consBan b1058 (consBan b1336 (consBan b1525 (consBan b3010 (consBan b1749 (consBan b3013 (consBan b1867 (consBan b1987 (consBan b3014 (consBan b2140 (consBan b3015 (consBan b2368 (consBan b2473 (consBan b1509 (consBan b3016 (consBan b1511 (consBan b1761 (consBan b2613 (consBan b2758 (consBan b3017 (consBan b3018 (consBan b3021 (consBan b3022 (consBan b2918 (consBan b3023 (consBan b3024 (consBan b3027 (consBan b3030 (consBan b3031 (consBan b3032 (consBan b3035 (consBan b3036 (consBan b1530 (consBan b3037 (consBan b1532 (consBan b3038 (consBan b3039 (consBan b3040 (consBan b1536 (consBan b3043 (consBan b1538 (consBan b2870 (consBan b3044 (consBan b3047 (consBan b1517 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3049:B 89 7 e2754:=viaPerm pt0 pti0 b1544 (by decide +kernel) (by decide +kernel)
theorem b3050:B 89 7 e2755:=viaPerm pt0 pti0 b1569 (by decide +kernel) (by decide +kernel)
theorem b3051:B 89 7 e2756:=viaPerm pt0 pti0 b1676 (by decide +kernel) (by decide +kernel)
theorem b3052:B 89 7 e2757:=viaPerm pt0 pti0 b1770 (by decide +kernel) (by decide +kernel)
theorem b3053:B 89 7 e2758:=viaPerm pt0 pti0 b1792 (by decide +kernel) (by decide +kernel)
theorem b3054:B 89 7 e2759:=viaPerm pt0 pti0 b1793 (by decide +kernel) (by decide +kernel)
theorem b3055:B 89 7 e2760:=viaPerm pt0 pti0 b1902 (by decide +kernel) (by decide +kernel)
theorem b3056:B 89 7 e2761:=viaPerm pt0 pti0 b1903 (by decide +kernel) (by decide +kernel)
theorem b3057:B 89 7 e1393:=viaPerm pt0 pti0 b2494 (by decide +kernel) (by decide +kernel)
theorem b3058:B 89 7 e2762:=viaPerm pt0 pti0 b2581 (by decide +kernel) (by decide +kernel)
theorem b3059:B 89 7 e2763:=viaPerm pt0 pti0 b2637 (by decide +kernel) (by decide +kernel)
theorem b3060:B 89 7 e1395:=viaPerm pt0 pti0 b2638 (by decide +kernel) (by decide +kernel)
theorem b3061:B 89 7 e2764:=viaPerm pt0 pti0 b2730 (by decide +kernel) (by decide +kernel)
theorem b3062:B 89 7 e2765:=viaPerm pt0 pti0 b2771 (by decide +kernel) (by decide +kernel)
theorem b3063:B 89 7 e1399:=viaPerm pt0 pti0 b2874 (by decide +kernel) (by decide +kernel)
theorem b3064:B 89 7 e2766:=viaPerm pt0 pti0 b2984 (by decide +kernel) (by decide +kernel)
theorem b3065:B 89 7 e1401:=viaPerm pt0 pti0 b2985 (by decide +kernel) (by decide +kernel)
theorem b3066:B 89 7 e2767:=viaPerm pt0 pti0 b3048 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3067:B 89 8 e2768:=viaBranch (ws:=[e17,e330,e384,e385,e76,e528,e580,e581,e582,e870,e960,e925,e610,e881,e1068,e1069,e1070,e1071,e1072,e1073,e1074,e1075,e1076,e1077,e1078,e1079,e1080,e1081,e1082,e1171,e1241,e1240,e1108,e1192,e1405,e1427,e1530,e1615,e1636,e1577,e1473,e1553,e1741,e1884,e1885,e1886,e1824,e1986,e1987,e1988,e1989,e2189,e2190,e2191,e2031,e2288,e1374,e2369,e2425,e1376,e2334,e2395,e2546,e2547,e2548,e2549,e2550,e2551,e2552,e2619,e2605,e2586,e1382,e2709,e1385,e2658,e2754,e2755,e2756,e2757,e2758,e2759,e2760,e2761,e1393,e2762,e2763,e1395,e2764,e2765,e1399,e2766,e1401,e2767]) (consBan b32 (consBan b375 (consBan b431 (consBan b432 (consBan b586 (consBan b587 (consBan b642 (consBan b643 (consBan b644 (consBan b960 (consBan b1067 (consBan b1068 (consBan b1181 (consBan b1182 (consBan b1183 (consBan b1184 (consBan b1185 (consBan b1186 (consBan b1187 (consBan b1188 (consBan b1189 (consBan b1190 (consBan b1191 (consBan b1192 (consBan b1193 (consBan b1194 (consBan b1195 (consBan b1196 (consBan b1197 (consBan b1290 (consBan b1361 (consBan b1362 (consBan b1483 (consBan b1543 (consBan b1544 (consBan b1569 (consBan b1676 (consBan b1770 (consBan b1792 (consBan b1793 (consBan b1902 (consBan b1903 (consBan b1904 (consBan b2053 (consBan b2054 (consBan b2055 (consBan b2157 (consBan b2158 (consBan b2159 (consBan b2160 (consBan b2161 (consBan b2385 (consBan b2386 (consBan b2387 (consBan b2492 (consBan b2493 (consBan b2494 (consBan b2581 (consBan b2637 (consBan b2638 (consBan b2730 (consBan b2771 (consBan b2772 (consBan b2773 (consBan b2774 (consBan b2775 (consBan b2776 (consBan b2777 (consBan b2778 (consBan b2871 (consBan b2872 (consBan b2873 (consBan b2874 (consBan b2984 (consBan b2985 (consBan b3048 (consBan b3049 (consBan b3050 (consBan b3051 (consBan b3052 (consBan b3053 (consBan b3054 (consBan b3055 (consBan b3056 (consBan b3057 (consBan b3058 (consBan b3059 (consBan b3060 (consBan b3061 (consBan b3062 (consBan b3063 (consBan b3064 (consBan b3065 (consBan b3066 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem sixWide : Wide 89 8 e2768 := widen (by decide +kernel) b3067
def certRows : List Nat := [9,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,17,17,17,17,17,17,17,17,17,20,20,20,20,20,20,20,20,24,24,24,24,24,24,24,24,24,24,33,33,33,33,33,33,33,33,33,34,34,34,34,34,34,34,34,36,36,36,36,36,36,36,36,40,40,40,40,40,40,40,40,40,40,48,48,48,48,48,48,48,48,48,48,0,3,5,7,8,12,16,18,32,0,3,6,7,8,12,18,32,0,3,5,7,8,12,16,18,32,0,5,6,7,12,16,18,32,0,3,5,6,7,8,12,16,18,32,0,3,5,7,8,12,16,18,32,0,3,6,7,8,12,18,32,0,5,6,7,12,16,18,32,0,3,5,6,7,8,12,16,18,32,0,3,5,6,7,8,12,16,18,32]
def certEtat : List ℕ := e2768
def certM : Nat := 89
def certFuel : Nat := 8

end PEqualNP.Outside.L_meta_28198.ArchivedClique

namespace PEqualNP.Outside.L_meta_28198.Reduce
namespace CliqueCertificate
open PEqualNP.Outside.L_meta_28198.ArchivedClique
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
    · exact PEqualNP.Outside.L_meta_28198.ArchivedClique.Live.done word_sep (by decide +kernel)
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
end PEqualNP.Outside.L_meta_28198.Reduce

theorem PEqualNP.Outside.L_meta_28198 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  apply PEqualNP.Outside.L_meta_28198.Frame.finish
  intro gs o legal computes hn
  obtain ⟨b,n,hlen,live⟩ := PEqualNP.Outside.L_meta_28198.freely_chain gs o legal computes hn
  obtain ⟨k,hk,T,sub,path⟩ := PEqualNP.Outside.L_meta_28198.Reduce.to_six live
  have low := PEqualNP.Outside.L_meta_28198.Reduce.CliqueCertificate.lower k T sub path
  omega

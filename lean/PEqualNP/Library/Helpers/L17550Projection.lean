import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.L17550Projection

abbrev Gate := Bool × Fin 32 × Fin 32
abbrev Pair := Fin 32 × Fin 32

def rawSeeds : List Nat :=
  [2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,
   26322415680,344922804352,414195942664,581968119809,1065151898146,371245215936,
   582520731713,1066477318818,549755842560,728266404032]

def seeds : List Nat :=
  [63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0]

def pos (i : Fin 11) : Nat := [0,1,2,3,4,5,8,9,10,11,15].getD i.val 0

def neg (i : Fin 10) : Nat := [16,17,18,19,28,31,32,35,37,39].getD i.val 0

def Rel (r s : Nat) : Prop :=
  (∀ i : Fin 11, s.testBit i.val = r.testBit (pos i)) ∧
  (∀ i : Fin 10, s.testBit (11+i.val) = true → r.testBit (neg i) = true)

instance (r s : Nat) : Decidable (Rel r s) := by unfold Rel; infer_instance

private theorem zeroRel : Rel 0 0 := by decide

private theorem andRel {a b u v : Nat} (ha : Rel a u) (hb : Rel b v) :
    Rel (a &&& b) (u &&& v) := by
  constructor
  · intro i
    simp [Nat.testBit_and, ha.1 i, hb.1 i]
  · intro i
    simp only [Nat.testBit_and, Bool.and_eq_true]
    exact fun h => ⟨ha.2 i h.1, hb.2 i h.2⟩

private theorem orRel {a b u v : Nat} (ha : Rel a u) (hb : Rel b v) :
    Rel (a ||| b) (u ||| v) := by
  constructor
  · intro i
    simp [Nat.testBit_or, ha.1 i, hb.1 i]
  · intro i
    simp only [Nat.testBit_or, Bool.or_eq_true]
    exact fun h => h.elim (fun h => Or.inl (ha.2 i h)) (fun h => Or.inr (hb.2 i h))

private theorem seedRel : List.Forall₂ Rel rawSeeds seeds := by decide

private theorem readRel {r s : List Nat} (h : List.Forall₂ Rel r s) (i : Nat) :
    Rel (r.getD i 0) (s.getD i 0) := by
  induction h generalizing i with
  | nil => simpa using zeroRel
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

def mulPair (w : List Nat) (p : Pair) := w.getD p.1.val 0 &&& w.getD p.2.val 0

def step (w : List Nat) (g : Gate) : List Nat :=
  w ++ [if g.1 = true then mulPair w g.2 else w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0]

def cover (w : List Nat) (pairs : List Pair) (start : Nat) :=
  pairs.foldl (fun acc p => acc ||| mulPair w p) start

private theorem pairRel {r s : List Nat} (h : List.Forall₂ Rel r s) (p : Pair) :
    Rel (mulPair r p) (mulPair s p) := andRel (readRel h _) (readRel h _)

private theorem snocRel {r s : List Nat} {a b : Nat} (h : List.Forall₂ Rel r s)
    (hab : Rel a b) : List.Forall₂ Rel (r ++ [a]) (s ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hxy _ ih => exact .cons hxy ih

private theorem runRel (gates : List Gate) {r s : List Nat} (h : List.Forall₂ Rel r s) :
    List.Forall₂ Rel (gates.foldl step r) (gates.foldl step s) := by
  induction gates generalizing r s with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    apply snocRel h
    by_cases hg : g.1 = true
    · simpa [hg] using pairRel h g.2
    · simpa [hg] using orRel (readRel h g.2.1.val) (readRel h g.2.2.val)

private theorem coverRel (pairs : List Pair) {r s : List Nat} (h : List.Forall₂ Rel r s)
    {a z : Nat} (ha : Rel a z) : Rel (cover r pairs a) (cover s pairs z) := by
  induction pairs generalizing a z with
  | nil => exact ha
  | cons p ps ih => exact ih (orRel ha (pairRel h p))

/-- Earlier-wire programs with one or fewer intermediate ANDs. The terminal tests
    refer only to retained truth-table positions. The projected AND may be clean. -/
def Admissible (gates : List Gate) (pairs : List Pair) : Prop :=
  let w := gates.foldl step seeds
  gates.length + 2*pairs.length ≤ 15 ∧
  (∀ i : Fin gates.length, (gates.get i).2.1.val < 16+i.val ∧
    (gates.get i).2.2.val < 16+i.val) ∧
  (gates.filter (fun g => g.1)).length ≤ 1 ∧
  (∀ p ∈ pairs, p.1.val < 16+gates.length ∧ p.2.val < 16+gates.length ∧
    ∀ j : Fin 10, (mulPair w p).testBit (11+j.val) = false) ∧
  ∀ j : Fin 11, (cover w pairs 0).testBit j.val = true

private theorem negMask : ∀ i : Fin 10, (1099511562240 : Nat).testBit (neg i) = true := by decide
private theorem posGoal : ∀ i : Fin 11, (65535 : Nat).testBit (pos i) = true := by decide
private theorem startRel : Rel 28864 0 := by decide

/-- The exact negative registered on the hub. -/
def Claim : Prop :=
  ¬ (∃ (x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x2 : List (Fin (32 : ℕ) × Fin (32 : ℕ))),   have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ), (371245215936 : ℕ), (582520731713 : ℕ), (1066477318818 : ℕ), (549755842560 : ℕ), (728266404032 : ℕ)] x1;   have x4 : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ := fun (x4 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x3.getD ↑x4.1 (0 : ℕ) &&& x3.getD ↑x4.2 (0 : ℕ);   x1.length + (2 : ℕ) * x2.length ≤ (15 : ℕ) ∧ (∀ (x5 : Fin x1.length), ↑(x1.get x5).2.1 < (16 : ℕ) + ↑x5 ∧ ↑(x1.get x5).2.2 < (16 : ℕ) + ↑x5) ∧ (List.filter (fun (x5 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5.1) x1).length = (1 : ℕ) ∧ (∀ (x5 : Fin x1.length), (x1.get x5).1 = Bool.true → x3.getD ((16 : ℕ) + ↑x5) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ)) ∧ (∀ x5 ∈ x2, ↑x5.1 < (16 : ℕ) + x1.length ∧ ↑x5.2 < (16 : ℕ) + x1.length ∧ x4 x5 &&& (1099511562240 : ℕ) = (0 : ℕ)) ∧ List.foldl (fun (x5 : ℕ) (x6 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ||| x4 x6) (28864 : ℕ) x2 = (65535 : ℕ))

/-- The four gate budgets and the unrestricted small-terminal exclusion suffice. -/
theorem of_exclusions
    (small : ∀ g p, Admissible g p → p.length ≤ 3 → False)
    (four : ∀ g p, Admissible g p → p.length = 4 → g.length ≤ 7 → False)
    (five : ∀ g p, Admissible g p → p.length = 5 → g.length ≤ 5 → False)
    (six : ∀ g p, Admissible g p → p.length = 6 → g.length ≤ 3 → False)
    (seven : ∀ g p, Admissible g p → p.length = 7 → g.length ≤ 1 → False) : Claim := by
  rintro ⟨g,p,hcost,hback,hone,_,hends,hgoal⟩
  have h := runRel g seedRel
  have had : Admissible g p := by
    refine ⟨hcost,hback,le_of_eq hone,?_,?_⟩
    · intro v hv
      obtain ⟨hl,hr,hclean⟩ := hends v hv
      refine ⟨hl,hr,?_⟩
      intro j
      by_contra! hn
      have hb := (pairRel h v).2 j (Bool.eq_true_of_not_eq_false hn)
      change mulPair (g.foldl step rawSeeds) v &&& 1099511562240 = 0 at hclean
      have hc := congrArg (fun a : Nat => a.testBit (neg j)) hclean
      simpa [Nat.testBit_and,hb,negMask] using hc
    · intro j
      change cover (g.foldl step rawSeeds) p 28864 = 65535 at hgoal
      simpa [hgoal,posGoal] using (coverRel p h startRel).1 j
  by_cases hp : p.length ≤ 3
  · exact small g p had hp
  · have hq : p.length = 4 ∨ p.length = 5 ∨ p.length = 6 ∨ p.length = 7 := by omega
    rcases hq with hq | hq | hq | hq
    · exact four g p had hq (by omega)
    · exact five g p had hq (by omega)
    · exact six g p had hq (by omega)
    · exact seven g p had hq (by omega)

end PEqualNP.MetaComplexity.L17550Projection

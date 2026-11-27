import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sum

namespace PEqualNP.Outside.L_pcx_345

open PEqualNP.ProofComplexity
open scoped BigOperators

private abbrev Raw {n : Nat} (k : Fin n → Nat) := (i : Fin n) × Fin (k i)
private abbrev Named {n : Nat} (A : Finset (Fin n)) := {i : Fin n // i ∈ A}
private abbrev Var {n : Nat} (k : Fin n → Nat) (A : Finset (Fin n)) := Raw k ⊕ Named A

private def parity {m : Nat} (x : Fin m → Bool) : Bool :=
  decide ((∑ j, (x j).toNat) % 2 = 1)

private lemma parity_cons {m : Nat} (b : Bool) (x : Fin m → Bool) :
    parity (Fin.cons b x) = xor b (parity x) := by
  simp only [parity, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  cases b
  · simp
  · let s := ∑ j, (x j).toNat
    change decide ((1 + s) % 2 = 1) = xor true (decide (s % 2 = 1))
    by_cases h : s % 2 = 1
    · have z : (1 + s) % 2 = 0 := by omega
      simp [h, z]
    · have o : (1 + s) % 2 = 1 := by omega
      simp [h, o]

private def fiber (m : Nat) (b : Bool) : Finset (Fin m → Bool) :=
  Finset.univ.filter (fun x => parity x = b)

private lemma fiber_mem {m : Nat} {b : Bool} {x : Fin m → Bool} :
    x ∈ fiber m b ↔ parity x = b := by simp [fiber]

private lemma fiber_card {m : Nat} (pos : 0 < m) (b : Bool) :
    (fiber m b).card = 2 ^ (m - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  let F : Finset (Fin d → Bool) := Finset.univ
  have h : F.card = (fiber (d + 1) b).card := by
    refine Finset.card_nbij' (fun x => Fin.cons (xor b (parity x)) x) Fin.tail ?_ ?_ ?_ ?_
    · intro x _
      change Fin.cons (xor b (parity x)) x ∈ fiber (d + 1) b
      rw [fiber_mem, parity_cons]
      cases b <;> cases parity x <;> decide
    · intro x _
      exact Finset.mem_univ _
    · intro x _
      exact Fin.tail_cons _ _
    · intro x hx
      have e : b = xor (x 0) (parity (Fin.tail x)) := by
        have e := parity_cons (x 0) (Fin.tail x)
        rwa [Fin.cons_self_tail, fiber_mem.mp hx] at e
      have first : xor b (parity (Fin.tail x)) = x 0 := by
        rw [e]
        cases x 0 <;> cases parity (Fin.tail x) <;> decide
      change Fin.cons (xor b (parity (Fin.tail x))) (Fin.tail x) = x
      rw [first, Fin.cons_self_tail]
  rw [← h]
  simp [F]

private noncomputable def block {m : Nat} (pos : 0 < m) (b : Bool) : Fin m → Bool :=
  (Finset.card_pos.mp (by rw [fiber_card pos b]; positivity : 0 < (fiber m b).card)).choose

private lemma block_parity {m : Nat} (pos : 0 < m) (b : Bool) : parity (block pos b) = b := by
  apply fiber_mem.mp
  exact (Finset.card_pos.mp (by rw [fiber_card pos b]; positivity : 0 < (fiber m b).card)).choose_spec

private def check {n : Nat} {k : Fin n → Nat} (x : Raw k → Bool) (i : Fin n) : Bool :=
  parity (fun j => x ⟨i, j⟩)

private def value {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)} (x : Raw k → Bool) :
    Var k A → Bool := Sum.elim x (fun i => check x i.val)

private def side {n : Nat} {k : Fin n → Nat} (b : Bool) (x : Raw k → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => check x i = b)

private lemma side_mem {n : Nat} {k : Fin n → Nat} {x : Raw k → Bool} {b : Bool} {i : Fin n} :
    i ∈ side b x ↔ check x i = b := by simp [side]

private lemma side_total {n : Nat} {k : Fin n → Nat} (x : Raw k → Bool) :
    (side true x).card + (side false x).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => check x i = true)
  simpa [side] using h

private def acceptable {n : Nat} {k : Fin n → Nat} (lo hi : Nat) (x : Raw k → Bool) : Prop :=
  lo ≤ (side true x).card ∧ (side true x).card ≤ hi

private def exactCNF {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)} (lo hi : Nat)
    (F : Finset (Clause (Var k A))) : Prop :=
  ∀ x : Raw k → Bool, acceptable lo hi x ↔ ∀ c ∈ F, ClauseSat (value x) c

private def threshold (n lo hi : Nat) (b : Bool) : Nat :=
  if b then hi + 1 else n - lo + 1

private def width {n : Nat} (k : Fin n → Nat) (A T : Finset (Fin n)) : Nat :=
  (T ∩ A).card + ∑ i ∈ T \ A, k i

private abbrev Tape {n : Nat} (k : Fin n → Nat) (R : Finset (Fin n)) :=
  (i : ↥R) → Fin (k i.val) → Bool

private abbrev Label {n : Nat} (k : Fin n → Nat) (A : Finset (Fin n)) :=
  Σ _ : Bool, Σ T : Finset (Fin n), Tape k (T \ A)

private def tapes {n : Nat} (k : Fin n → Nat) (R : Finset (Fin n)) (b : Bool) :
    Finset (Tape k R) := Fintype.piFinset (fun i : ↥R => fiber (k i.val) b)

private lemma tapes_mem {n : Nat} {k : Fin n → Nat} {R : Finset (Fin n)} {b : Bool}
    {t : Tape k R} : t ∈ tapes k R b ↔ ∀ i, parity (t i) = b := by
  simp only [tapes, Fintype.mem_piFinset, fiber_mem]

private lemma tapes_card {n : Nat} {k : Fin n → Nat} (pos : ∀ i, 0 < k i)
    (R : Finset (Fin n)) (b : Bool) :
    (tapes k R b).card = 2 ^ (∑ i ∈ R, (k i - 1)) := by
  rw [tapes, Fintype.card_piFinset]
  simp_rw [fiber_card (pos (_ : ↥R).val)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_attach R (fun i => k i - 1)

private noncomputable def labels {n : Nat} (k : Fin n → Nat) (A : Finset (Fin n))
    (lo hi : Nat) : Finset (Label k A) := by
  classical
  exact Finset.univ.sigma (fun b => ((Finset.univ : Finset (Fin n)).powersetCard
    (threshold n lo hi b)).sigma (fun T => tapes k (T \ A) b))

private lemma label_mem {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)} {lo hi : Nat}
    {p : Label k A} : p ∈ labels k A lo hi ↔
    p.2.1.card = threshold n lo hi p.1 ∧ ∀ i, parity (p.2.2 i) = p.1 := by
  simp [labels, Finset.mem_sigma, Finset.mem_powersetCard, tapes_mem]

private def contribution {n : Nat} (k : Fin n → Nat) (A : Finset (Fin n)) (s w : Nat) : Nat :=
  ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
    if w ≤ width k A T then 2 ^ (∑ i ∈ T \ A, (k i - 1)) else 0

private lemma label_count {n : Nat} {k : Fin n → Nat} (pos : ∀ i, 0 < k i)
    (A : Finset (Fin n)) (lo hi w : Nat) :
    ((labels k A lo hi).filter (fun p => w ≤ width k A p.2.1)).card =
      contribution k A (hi + 1) w + contribution k A (n - lo + 1) w := by
  classical
  have repr : (labels k A lo hi).filter (fun p => w ≤ width k A p.2.1) =
      Finset.univ.sigma (fun b => (((Finset.univ : Finset (Fin n)).powersetCard
        (threshold n lo hi b)).filter (fun T => w ≤ width k A T)).sigma
          (fun T => tapes k (T \ A) b)) := by
    ext p
    simp only [labels, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter]
    tauto
  rw [repr, Finset.card_sigma]
  simp_rw [Finset.card_sigma, tapes_card pos, Finset.sum_filter]
  simp [threshold, contribution]

private noncomputable def fill {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) (p : Label k A) : Raw k → Bool :=
  fun z => if hz : z.1 ∈ p.2.1 \ A then p.2.2 ⟨z.1, hz⟩ z.2
    else block (pos z.1) (if z.1 ∈ p.2.1 then p.1 else !p.1) z.2

private lemma filled_side {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) {lo hi : Nat} {p : Label k A} (hp : p ∈ labels k A lo hi)
    (i : Fin n) : check (fill pos p) i = if i ∈ p.2.1 then p.1 else !p.1 := by
  classical
  by_cases hz : i ∈ p.2.1 \ A
  · simp only [check, fill, dite_eq_left hz, ite_eq_left (Finset.mem_sdiff.mp hz).1]
    exact (label_mem.mp hp).2 ⟨i, hz⟩
  · let b := if i ∈ p.2.1 then p.1 else !p.1
    have eq : (fun j : Fin (k i) => fill pos p ⟨i, j⟩) = block (pos i) b := by
      funext j
      simp only [fill, dite_eq_right hz, b]
    change parity (fun j => fill pos p ⟨i, j⟩) = b
    rw [eq]
    exact block_parity (pos i) b

private lemma side_fill {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) {lo hi : Nat} {p : Label k A} (hp : p ∈ labels k A lo hi) :
    side p.1 (fill pos p) = p.2.1 := by
  ext i
  rw [side_mem, filled_side pos hp]
  by_cases h : i ∈ p.2.1 <;> cases p.1 <;> simp [h]

private def vars {n : Nat} (k : Fin n → Nat) (A T : Finset (Fin n)) : Finset (Var k A) :=
  ((T \ A).sigma (fun i => (Finset.univ : Finset (Fin (k i))))).disjSum
    ((Finset.univ : Finset (Named A)).filter (fun i => i.val ∈ T))

private lemma raw_mem {n : Nat} {k : Fin n → Nat} {A T : Finset (Fin n)} {z : Raw k} :
    Sum.inl z ∈ vars k A T ↔ z.1 ∈ T \ A := by simp [vars, Finset.mem_sigma]

private lemma named_mem {n : Nat} {k : Fin n → Nat} {A T : Finset (Fin n)} {z : Named A} :
    Sum.inr z ∈ vars k A T ↔ z.val ∈ T := by simp [vars]

private lemma vars_card {n : Nat} (k : Fin n → Nat) (A T : Finset (Fin n)) :
    (vars k A T).card = width k A T := by
  let names := (Finset.univ : Finset (Named A)).filter (fun i => i.val ∈ T)
  have eq : names.image Subtype.val = T ∩ A := by
    ext i
    simp only [Finset.mem_image, names, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    constructor
    · rintro ⟨j, hm, rfl⟩
      exact ⟨hm, j.property⟩
    · rintro ⟨hi, ha⟩
      exact ⟨⟨i, ha⟩, hi, rfl⟩
  have nc : names.card = (T ∩ A).card := by
    rw [← eq, Finset.card_image_of_injective _ Subtype.val_injective]
  unfold vars width
  rw [Finset.card_disjSum, Finset.card_sigma]
  change (∑ i ∈ T \ A, (Finset.univ : Finset (Fin (k i))).card) + names.card = _
  simp [nc, Nat.add_comm]

private noncomputable def clause {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) (p : Label k A) : Clause (Var k A) :=
  (vars k A p.2.1).image (fun v => (v, !(value (A := A) (fill pos p) v)))

private lemma clause_width {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) (p : Label k A) : (clause pos p).card = width k A p.2.1 := by
  rw [clause, Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq), vars_card]

private lemma bool_ne_not (a b : Bool) : a ≠ !b ↔ a = b := by
  cases a <;> cases b <;> decide

private lemma false_clause {V : Type} {a : V → Bool} {c : Clause V} :
    ¬ ClauseSat a c ↔ ∀ l ∈ c, a l.1 ≠ l.2 := by
  simp only [ClauseSat, not_exists, not_and]

private lemma false_canonical {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) (p : Label k A) (x : Raw k → Bool) :
    ¬ ClauseSat (value (A := A) x) (clause pos p) ↔
      ∀ v ∈ vars k A p.2.1, value (A := A) x v = value (fill pos p) v := by
  rw [false_clause]
  constructor
  · intro h v hv
    exact (bool_ne_not _ _).mp (h _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  · intro h l hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
    exact (bool_ne_not _ _).mpr (h v hv)

private lemma agreement_check {n : Nat} {k : Fin n → Nat} {A T : Finset (Fin n)}
    {x y : Raw k → Bool} (agree : ∀ v ∈ vars k A T, value (A := A) x v = value y v)
    {i : Fin n} (hi : i ∈ T) : check x i = check y i := by
  by_cases hA : i ∈ A
  · exact agree (Sum.inr ⟨i, hA⟩) (named_mem.mpr hi)
  · unfold check
    congr 1
    funext j
    exact agree (Sum.inl ⟨i, j⟩) (raw_mem.mpr (Finset.mem_sdiff.mpr ⟨hi, hA⟩))

private lemma allowed_below {n : Nat} {k : Fin n → Nat} {lo hi : Nat} {x : Raw k → Bool}
    (good : acceptable lo hi x) (b : Bool) :
    (side b x).card < threshold n lo hi b := by
  have h := side_total x
  obtain ⟨_, _⟩ := good
  cases b <;> simp only [threshold, Bool.false_eq_true, ↓reduceIte] <;> omega

private lemma outside_bound {n : Nat} {k : Fin n → Nat} {lo hi : Nat} {x : Raw k → Bool}
    (ln : lo ≤ n) (bad : ¬ acceptable lo hi x) :
    ∃ b, threshold n lo hi b ≤ (side b x).card := by
  have h := side_total x
  unfold acceptable at bad
  by_cases low : lo ≤ (side true x).card
  · exact ⟨true, by simp [threshold]; omega⟩
  · exact ⟨false, by simp [threshold]; omega⟩

private lemma exact_construction {n : Nat} {k : Fin n → Nat} (A : Finset (Fin n))
    (pos : ∀ i, 0 < k i) (lo hi : Nat) (ln : lo ≤ n) :
    exactCNF lo hi ((labels k A lo hi).image (clause pos)) := by
  classical
  intro x
  constructor
  · intro good c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    by_contra h
    have agree := (false_canonical pos p x).mp h
    have sub : p.2.1 ⊆ side p.1 x := by
      intro i hi
      exact side_mem.mpr ((agreement_check agree hi).trans (by rw [filled_side pos hp, ite_eq_left hi]))
    have le := Finset.card_le_card sub
    rw [(label_mem.mp hp).1] at le
    exact (allowed_below good p.1).not_ge le
  · intro sat
    by_contra bad
    obtain ⟨b, le⟩ := outside_bound ln bad
    obtain ⟨T, hT, cardT⟩ := Finset.exists_subset_card_eq le
    let p : Label k A := ⟨b, T, fun i j => x ⟨i.val, j⟩⟩
    have hp : p ∈ labels k A lo hi := by
      apply label_mem.mpr
      exact ⟨cardT, fun i => side_mem.mp (hT (Finset.mem_sdiff.mp i.property).1)⟩
    have notSat : ¬ ClauseSat (value (A := A) x) (clause pos p) := by
      apply (false_canonical pos p x).mpr
      intro v hv
      rcases v with r | i
      · have hr := raw_mem.mp hv
        change x r = fill pos p r
        simp [fill, hr, p]
      · have hi := named_mem.mp hv
        change check x i.val = check (fill pos p) i.val
        rw [filled_side pos hp, ite_eq_left hi]
        exact side_mem.mp (hT hi)
    exact notSat (sat _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

private lemma separates {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)} (lo hi : Nat)
    (order : lo ≤ hi) (range : hi ≤ n) (pos : ∀ i, 0 < k i)
    {p q : Label k A} (hp : p ∈ labels k A lo hi) (hq : q ∈ labels k A lo hi)
    (agree : ∀ v ∈ vars k A p.2.1,
      value (A := A) (fill pos q) v = value (fill pos p) v) : p = q := by
  classical
  have incl : p.2.1 ⊆ side p.1 (fill pos q) := by
    intro i h
    apply side_mem.mpr
    rw [agreement_check agree h, filled_side pos hp, ite_eq_left h]
  have same : p.1 = q.1 := by
    by_contra different
    have disj : Disjoint p.2.1 q.2.1 := Finset.disjoint_left.mpr (fun i hi hj =>
      different ((side_mem.mp (incl hi)).symm.trans (side_mem.mp ((side_fill pos hq).symm ▸ hj))))
    have le : p.2.1.card + q.2.1.card ≤ n := by
      rw [← Finset.card_union_of_disjoint disj]
      simpa using Finset.card_le_univ (p.2.1 ∪ q.2.1)
    rw [(label_mem.mp hp).1, (label_mem.mp hq).1] at le
    cases b : p.1 <;> cases c : q.1 <;> simp [b, c, threshold] at different le <;> omega
  have subset : p.2.1 ⊆ q.2.1 := by simpa only [same, side_fill pos hq] using incl
  have equal : p.2.1 = q.2.1 := by
    apply Finset.eq_of_subset_of_card_le subset
    rw [(label_mem.mp hp).1, (label_mem.mp hq).1, same]
  rcases p with ⟨b, T, u⟩
  rcases q with ⟨c, S, v⟩
  change b = c at same
  change T = S at equal
  subst c S
  have tape_eq : v = u := by
    funext i j
    have h := agree (Sum.inl ⟨i.val, j⟩) (raw_mem.mpr i.property)
    change fill pos (⟨b, T, v⟩ : Label k A) ⟨i.val, j⟩ =
      fill pos (⟨b, T, u⟩ : Label k A) ⟨i.val, j⟩ at h
    simpa [fill, i.property] using h
  rw [tape_eq]

private def flip {n : Nat} {k : Fin n → Nat} (x : Raw k → Bool) (z : Raw k) : Raw k → Bool :=
  Function.update x z (!(x z))

private lemma parity_flip {m : Nat} (x : Fin m → Bool) (j : Fin m) :
    parity (Function.update x j (!(x j))) = !parity x := by
  let R := (Finset.univ : Finset (Fin m)).erase j
  let s := ∑ i ∈ R, (x i).toNat
  have old : (∑ i, (x i).toNat) = s + (x j).toNat :=
    (Finset.sum_erase_add _ (fun i => (x i).toNat) (Finset.mem_univ j)).symm
  let y := Function.update x j (!(x j))
  have eqSum : (∑ i ∈ R, (y i).toNat) = s := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [y, Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have new : (∑ i, (y i).toNat) = s + (!(x j)).toNat := by
    rw [← Finset.sum_erase_add _ (fun i => (y i).toNat) (Finset.mem_univ j)]
    change (∑ i ∈ R, (y i).toNat) + (y j).toNat = _
    rw [eqSum]
    simp [y]
  change parity y = !parity x
  rw [parity, parity, old, new]
  by_cases ho : s % 2 = 1
  · have h : (s + 1) % 2 = 0 := by omega
    cases x j <;> simp [ho, h]
  · have h : (s + 1) % 2 = 1 := by omega
    cases x j <;> simp [ho, h]

private lemma check_other {n : Nat} {k : Fin n → Nat} (x : Raw k → Bool) (z : Raw k)
    {i : Fin n} (ne : i ≠ z.1) : check (flip x z) i = check x i := by
  unfold check
  congr 1
  funext j
  have neq : (⟨i, j⟩ : Raw k) ≠ z := fun e => ne (congrArg Sigma.fst e)
  exact Function.update_of_ne neq _ _

private lemma check_flipped {n : Nat} {k : Fin n → Nat} (x : Raw k → Bool)
    (i : Fin n) (r : Fin (k i)) : check (flip x ⟨i, r⟩) i = !check x i := by
  let t : Fin (k i) → Bool := fun j => x ⟨i, j⟩
  change parity (fun j => flip x (⟨i, r⟩ : Raw k) ⟨i, j⟩) = !parity t
  have eq : (fun j => flip x (⟨i, r⟩ : Raw k) ⟨i, j⟩) =
      Function.update t r (!(t r)) := by
    funext j
    by_cases hj : j = r
    · subst j
      simp [flip, t]
    · have ne : (⟨i, j⟩ : Raw k) ≠ ⟨i, r⟩ := by simpa using hj
      simp [flip, t, Function.update_of_ne hj, Function.update_of_ne ne]
  rw [eq, parity_flip]

private lemma repaired {n : Nat} {k : Fin n → Nat} {lo hi : Nat}
    (order : lo ≤ hi) (range : hi ≤ n) (x : Raw k → Bool) (b : Bool) (i : Fin n)
    (j : Fin (k i)) (inside : i ∈ side b x)
    (card : (side b x).card = threshold n lo hi b) :
    acceptable lo hi (flip x ⟨i, j⟩) := by
  have update : side b (flip x ⟨i, j⟩) = (side b x).erase i := by
    ext v
    rw [side_mem, Finset.mem_erase]
    by_cases hv : v = i
    · subst v
      rw [check_flipped, side_mem.mp inside]
      cases b <;> simp
    · rw [check_other x ⟨i, j⟩ hv, ← side_mem]
      simp [hv]
  have h := Finset.card_erase_add_one inside
  rw [← update, card] at h
  have both := side_total (flip x ⟨i, j⟩)
  unfold acceptable
  cases b <;> simp only [threshold, Bool.false_eq_true, ↓reduceIte] at h <;> omega

private def guarded {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (x : Raw k → Bool) (c : Clause (Var k A)) (i : Fin n) : Prop :=
  (∀ j : Fin (k i), (Sum.inl ⟨i, j⟩, !(x ⟨i, j⟩)) ∈ c) ∨
  ∃ h : i ∈ A, (Sum.inr ⟨i, h⟩, !check x i) ∈ c

private lemma critical_guarded {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    {F : Finset (Clause (Var k A))} {lo hi : Nat} (specific : exactCNF lo hi F)
    (order : lo ≤ hi) (range : hi ≤ n) (pos : ∀ i, 0 < k i) {p : Label k A}
    (hp : p ∈ labels k A lo hi) {c : Clause (Var k A)} (hc : c ∈ F)
    (bad : ¬ ClauseSat (value (A := A) (fill pos p)) c)
    {i : Fin n} (in_T : i ∈ p.2.1) : guarded (fill pos p) c i := by
  classical
  let x := fill pos p
  by_cases named : ∃ h : i ∈ A, (Sum.inr ⟨i, h⟩, !check x i) ∈ c
  · exact Or.inr named
  · left
    intro j
    let y := flip x (⟨i, j⟩ : Raw k)
    have okay : acceptable lo hi y := by
      have h := side_fill pos hp
      apply repaired order range x p.1 i j
      · rwa [h]
      · rw [h, (label_mem.mp hp).1]
    obtain ⟨⟨v, sign⟩, hLit, good⟩ := (specific y).mp okay c hc
    have old : value (A := A) x v ≠ sign := (false_clause.mp bad) _ hLit
    rcases v with r | t
    · have eq : r = ⟨i, j⟩ := by
        by_contra ne
        apply old
        simpa [y, value, flip, Function.update_of_ne ne] using good
      subst r
      have e : sign = !(x ⟨i, j⟩) := by simpa [y, value, flip] using good.symm
      rwa [e] at hLit
    · have eq : t.val = i := by
        by_contra ne
        apply old
        have new : check y t.val = sign := good
        rwa [show check y t.val = check x t.val from check_other x ⟨i, j⟩ ne] at new
      have new : check y t.val = sign := good
      have e : sign = !check x i := by rw [eq, show check y i = !check x i from check_flipped x i j] at new; exact new.symm
      have memA : i ∈ A := eq ▸ t.property
      have same : t = (⟨i, memA⟩ : Named A) := Subtype.ext eq
      exact False.elim (named ⟨memA, by simpa only [← same, ← e] using hLit⟩)

private lemma raw_agreement {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    {x y : Raw k → Bool} {c : Clause (Var k A)}
    (hy : ¬ ClauseSat (value (A := A) y) c) {i : Fin n}
    (all : ∀ j : Fin (k i), (Sum.inl ⟨i, j⟩, !(x ⟨i, j⟩)) ∈ c)
    (j : Fin (k i)) : y ⟨i, j⟩ = x ⟨i, j⟩ :=
  (bool_ne_not _ _).mp (false_clause.mp hy _ (all j))

private lemma guarded_agreement {n : Nat} {k : Fin n → Nat} {A T : Finset (Fin n)}
    {x y : Raw k → Bool} {c : Clause (Var k A)}
    (all : ∀ i ∈ T, guarded x c i) (hy : ¬ ClauseSat (value (A := A) y) c) :
    ∀ v ∈ vars k A T, value (A := A) y v = value x v := by
  intro v hv
  rcases v with z | i
  · have hz := Finset.mem_sdiff.mp (raw_mem.mp hv)
    rcases all z.1 hz.1 with raw | ⟨h, _⟩
    · exact raw_agreement hy raw z.2
    · exact False.elim (hz.2 h)
  · rcases all i.val (named_mem.mp hv) with raw | ⟨h, hc⟩
    · change check y i.val = check x i.val
      unfold check
      congr 1
      funext j
      exact raw_agreement hy raw j
    · exact (bool_ne_not _ _).mp (false_clause.mp hy _ hc)

private def projected {n : Nat} {k : Fin n → Nat} {A : Finset (Fin n)}
    (l : Literal (Var k A)) : Var k A :=
  match l.1 with
  | Sum.inl z => if h : z.1 ∈ A then Sum.inr ⟨z.1, h⟩ else Sum.inl z
  | Sum.inr i => Sum.inr i

private lemma guarded_width {n : Nat} {k : Fin n → Nat} {A T : Finset (Fin n)}
    (pos : ∀ i, 0 < k i) {x : Raw k → Bool} {c : Clause (Var k A)}
    (all : ∀ i ∈ T, guarded x c i) : width k A T ≤ c.card := by
  have sub : vars k A T ⊆ c.image projected := by
    intro v hv
    rcases v with z | i
    · have hz := Finset.mem_sdiff.mp (raw_mem.mp hv)
      rcases all z.1 hz.1 with raw | ⟨h, _⟩
      · exact Finset.mem_image.mpr ⟨_, raw z.2, by simp [projected, hz.2]⟩
      · exact False.elim (hz.2 h)
    · rcases all i.val (named_mem.mp hv) with raw | ⟨h, hc⟩
      · let j : Fin (k i.val) := ⟨0, pos i.val⟩
        exact Finset.mem_image.mpr ⟨_, raw j, by simp [projected, i.property]⟩
      · exact Finset.mem_image.mpr ⟨_, hc, rfl⟩
  rw [← vars_card]
  exact (Finset.card_le_card sub).trans Finset.card_image_le

private lemma counts_lower {n : Nat} {k : Fin n → Nat} (A : Finset (Fin n))
    (pos : ∀ i, 0 < k i) (lo hi : Nat) (order : lo ≤ hi) (range : hi ≤ n)
    (F : Finset (Clause (Var k A))) (specific : exactCNF lo hi F) (w : Nat) :
    contribution k A (hi + 1) w + contribution k A (n - lo + 1) w ≤
      (F.filter (fun c => w ≤ c.card)).card := by
  classical
  have reject (p : Label k A) (hp : p ∈ labels k A lo hi) :
      ∃ c ∈ F, ¬ ClauseSat (value (A := A) (fill pos p)) c := by
    by_contra no
    have good : acceptable lo hi (fill pos p) := (specific _).mpr (fun c hc => by
      by_contra h
      exact no ⟨c, hc, h⟩)
    have less := allowed_below good p.1
    rw [side_fill pos hp, (label_mem.mp hp).1] at less
    exact (Nat.lt_irrefl _) less
  let choose (p : Label k A) : Clause (Var k A) :=
    if hp : p ∈ labels k A lo hi then (reject p hp).choose else ∅
  have fact (p : Label k A) (hp : p ∈ labels k A lo hi) :
      choose p ∈ F ∧ ¬ ClauseSat (value (A := A) (fill pos p)) (choose p) := by
    simpa only [choose, dite_eq_left hp] using (reject p hp).choose_spec
  rw [← label_count pos A lo hi w]
  apply Finset.card_le_card_of_injOn choose
  · intro p hp
    obtain ⟨hp, width_le⟩ := Finset.mem_filter.mp hp
    obtain ⟨mem, bad⟩ := fact p hp
    exact Finset.mem_filter.mpr ⟨mem, width_le.trans (guarded_width pos
      (fun i hi => critical_guarded specific order range pos hp mem bad hi))⟩
  · intro p hp q hq eq
    have p_mem := (Finset.mem_filter.mp hp).1
    have q_mem := (Finset.mem_filter.mp hq).1
    obtain ⟨mem, bad⟩ := fact p p_mem
    have nextBad := (fact q q_mem).2
    rw [← eq] at nextBad
    exact separates lo hi order range pos p_mem q_mem (guarded_agreement
      (fun i hi => critical_guarded specific order range pos p_mem mem bad hi) nextBad)

private lemma counts_upper {n : Nat} {k : Fin n → Nat} (A : Finset (Fin n))
    (pos : ∀ i, 0 < k i) (lo hi : Nat) (order : lo ≤ hi) (range : hi ≤ n) (w : Nat) :
    (((labels k A lo hi).image (clause pos)).filter (fun c => w ≤ c.card)).card =
      contribution k A (hi + 1) w + contribution k A (n - lo + 1) w := by
  classical
  have same : ((labels k A lo hi).image (clause pos)).filter (fun c => w ≤ c.card) =
      ((labels k A lo hi).filter (fun p => w ≤ width k A p.2.1)).image (clause pos) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, h⟩
      exact ⟨p, ⟨hp, by rwa [clause_width] at h⟩, rfl⟩
    · rintro ⟨p, ⟨hp, h⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, by rwa [clause_width]⟩
  rw [same, Finset.card_image_of_injOn, label_count pos]
  intro p hp q hq eq
  have h := (false_canonical pos q (fill pos q)).mpr (fun _ _ => rfl)
  rw [← eq] at h
  exact separates lo hi order range pos (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
    ((false_canonical pos p (fill pos q)).mp h)

end PEqualNP.Outside.L_pcx_345

open PEqualNP.Outside.L_pcx_345 in
theorem PEqualNP.Outside.L_pcx_345 : (∀ (n : ℕ) (k : Fin n → ℕ) (A : Finset (Fin n)) (lo hi : ℕ),
  (∀ i, 0 < k i) → lo ≤ hi → hi ≤ n →
  let Raw := (i : Fin n) × Fin (k i)
  let Named := {i : Fin n // i ∈ A}
  let V := Raw ⊕ Named
  let check := fun (x : Raw → Bool) (i : Fin n) =>
    decide ((∑ j : Fin (k i), (x ⟨i,j⟩).toNat) % 2 = 1)
  let exact := fun (F : Finset (PEqualNP.ProofComplexity.Clause V)) =>
    ∀ x : Raw → Bool,
      let d := (Finset.univ.filter (fun i : Fin n => check x i = true)).card
      let values := Sum.elim x (fun i : Named => check x i.val)
      (lo ≤ d ∧ d ≤ hi) ↔ ∀ c ∈ F, PEqualNP.ProofComplexity.ClauseSat values c
  let tailCount := fun (s w : ℕ) =>
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
      let raw := T \ A
      let width := (T ∩ A).card + ∑ i ∈ raw, k i
      if w ≤ width then 2^(∑ i ∈ raw, (k i-1)) else 0
  let bound := fun w : ℕ => tailCount (hi+1) w + tailCount (n-lo+1) w
  let wide := fun (F : Finset (PEqualNP.ProofComplexity.Clause V)) (w : ℕ) =>
    (F.filter (fun c => w ≤ c.card)).card
  (∃ F : Finset (PEqualNP.ProofComplexity.Clause V), exact F ∧
    ∀ w : ℕ, wide F w = bound w) ∧
  (∀ F : Finset (PEqualNP.ProofComplexity.Clause V), exact F →
    ∀ w : ℕ, bound w ≤ wide F w)) := by
  classical
  intro n k A lo hi pos order range R N V test exact tailCount bound wide
  constructor
  · refine ⟨(labels k A lo hi).image (clause pos), ?_, ?_⟩
    · exact exact_construction A pos lo hi (order.trans range)
    · exact counts_upper A pos lo hi order range
  · intro F hF
    exact counts_lower A pos lo hi order range F hF

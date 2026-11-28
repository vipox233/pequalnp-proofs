import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_447_aux

private lemma card_pair_eq_choose (t : ℕ) :
    Fintype.card {p : Fin t × Fin t // p.1 < p.2} = t.choose 2 := by
  have h1 : Fintype.card {p : Fin t × Fin t // p.1 < p.2} =
      (Finset.powersetCard 2 (Finset.univ : Finset (Fin t))).card := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun p _ => ({p.1.1, p.1.2} : Finset (Fin t))) ?_ ?_ ?_
    · intro p _
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair (ne_of_lt p.2)⟩
    · intro p1 _ p2 _ heq
      have h1_mem : p1.1.1 ∈ ({p2.1.1, p2.1.2} : Finset (Fin t)) :=
        heq ▸ Finset.mem_insert_self _ _
      have h2_mem : p1.1.2 ∈ ({p2.1.1, p2.1.2} : Finset (Fin t)) :=
        heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1_mem h2_mem
      have hlt1 := p1.2
      have hlt2 := p2.2
      apply Subtype.ext
      rcases h1_mem with h1a | h1b <;> rcases h2_mem with h2a | h2b
      · exact absurd (h1a.trans h2a.symm) (ne_of_lt hlt1)
      · exact Prod.ext h1a h2b
      · exfalso; rw [h1b, h2a] at hlt1; exact absurd hlt1 (not_lt.mpr (le_of_lt hlt2))
      · exact absurd (h1b.trans h2b.symm) (ne_of_lt hlt1)
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      rcases Finset.card_eq_two.mp hs.2 with ⟨a, b, hab, rfl⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨⟨(a, b), hlt⟩, Finset.mem_univ _, rfl⟩
      · refine ⟨⟨(b, a), hgt⟩, Finset.mem_univ _, ?_⟩
        ext x; simp [or_comm]
  rw [h1, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma prod_fin3_eq {α : Type*} [CommMonoid α] (f : Fin 3 → α) :
    ∏ k : Fin 3, f k = f 0 * f 1 * f 2 := by
  rw [Fin.prod_univ_three]

private lemma obs_formula {t : ℕ}
    (g : Option {p : Fin t × Fin t // p.1 < p.2}) (P : Finset (Fin t)) (l : ℕ) :
    let T := Fin t
    let V := Option (T × Bool)
    let E := Fin 3 × T
    let tail := fun e : E => if e.1 = 0 then some (e.2, false) else (none : V)
    let head := fun e : E => some (e.2, decide (e.1 ≠ 1))
    let weight := fun (e : E) (diff : Bool) =>
      if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
      if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
        (if diff then 1 else 3) else (2 : ℕ)
    (∑ x : V → Bool, if (∀ i ∈ P, x (some (i, false)) = false) ∧
        (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = l then
        ∏ e : E, weight e (xor (x (tail e)) (x (head e))) else 0) =
      if l = 2 * t then
        ∑ h : Bool, ∏ i : T,
          (if i ∈ P then weight (1, i) (xor h false) else 4)
      else 0 := by
  dsimp only
  let T := Fin t
  let V := Option (T × Bool)
  let E := Fin 3 × T
  let tail : E → V := fun e => if e.1 = 0 then some (e.2, false) else none
  let head : E → V := fun e => some (e.2, decide (e.1 ≠ 1))
  let weight : E → Bool → ℕ := fun e diff =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let goodSpin : (V → Bool) → Prop := fun x => ∀ i : T, x (some (i, true)) = !(x (some (i, false)))
  have hzero_bad : ∀ x : V → Bool, ¬ goodSpin x →
      ∏ e : E, weight e (xor (x (tail e)) (x (head e))) = 0 := by
    intro x hbad
    simp only [goodSpin, not_forall] at hbad
    rcases hbad with ⟨i0, hi0⟩
    refine Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin 3), i0)) ?_
    dsimp only [weight, tail, head]
    simp only [↓reduceIte]
    have heq : x (some (i0, false)) = x (some (i0, true)) := by
      cases h1 : x (some (i0, false)) <;> cases h2 : x (some (i0, true)) <;> simp [h1, h2] at hi0 ⊢
    rw [heq]
    simp
  have hdiff_good : ∀ x : V → Bool, goodSpin x →
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2 * t := by
    intro x hgx
    have hfib : (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card =
        ∑ i : T, ((Finset.univ : Finset (Fin 3)).filter (fun k => x (tail (k, i)) ≠ x (head (k, i)))).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        rcases he with ⟨hne, rfl⟩
        exact hne
      · intro e1 he1 e2 he2 heq
        simp only [Finset.mem_filter] at he1 he2
        exact Prod.ext heq (he1.2.trans he2.2.symm)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨(k, i), ?_, rfl⟩
        simp [hk]
    rw [hfib]
    have heach2 : ∀ i : T,
        ((Finset.univ : Finset (Fin 3)).filter (fun k => x (tail (k, i)) ≠ x (head (k, i)))).card = 2 := by
      intro i
      have hgi := hgx i
      have hcard : ((Finset.univ : Finset (Fin 3)).filter (fun k => x (tail (k, i)) ≠ x (head (k, i)))).card =
          ∑ k : Fin 3, if x (tail (k, i)) ≠ x (head (k, i)) then 1 else 0 := by
        rw [Finset.card_filter]
      rw [hcard, Fin.sum_univ_three]
      dsimp only [tail, head]
      have h01 : decide ((0 : Fin 3) ≠ 1) = true := rfl
      have h11 : decide ((1 : Fin 3) ≠ 1) = false := rfl
      have h21 : decide ((2 : Fin 3) ≠ 1) = true := rfl
      have h10 : ((1 : Fin 3) ≠ 0) := by decide
      have h20 : ((2 : Fin 3) ≠ 0) := by decide
      simp only [h01, h11, h21, h10, h20, ↓reduceIte]
      rw [hgi]
      cases x none <;> cases x (some (i, false)) <;> decide
    rw [Finset.sum_congr rfl (fun i _ => heach2 i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_comm]
  have hprod_good : ∀ x : V → Bool, goodSpin x →
      ∏ e : E, weight e (xor (x (tail e)) (x (head e))) =
        ∏ i : T, weight (1, i) (xor (x none) (x (some (i, false)))) := by
    intro x hgx
    rw [Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_three]
    have hgi := hgx i
    have h0 : weight (0, i) (xor (x (tail (0, i))) (x (head (0, i)))) = 1 := by
      dsimp only [weight, tail, head]
      have h01 : decide ((0 : Fin 3) ≠ 1) = true := rfl
      simp only [h01, ↓reduceIte]
      rw [hgi]
      cases x (some (i, false)) <;> rfl
    have h2 : weight (2, i) (xor (x (tail (2, i))) (x (head (2, i)))) = 1 := by
      dsimp only [weight]
      have h20 : ((2 : Fin 3) ≠ 0) := by decide
      simp [h20]
    have h1 : weight (1, i) (xor (x (tail (1, i))) (x (head (1, i)))) =
        weight (1, i) (xor (x none) (x (some (i, false)))) := by
      dsimp only [tail, head]
      have h10 : ((1 : Fin 3) ≠ 0) := by decide
      simp [h10]
    rw [h0, h1, h2, one_mul, mul_one]
  by_cases hl : l = 2 * t
  · subst hl
    simp only [↓reduceIte]
    have hsum_good : (∑ x : V → Bool, if (∀ i ∈ P, x (some (i, false)) = false) ∧
          (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2 * t then
          ∏ e : E, weight e (xor (x (tail e)) (x (head e))) else 0) =
        ∑ x ∈ (Finset.univ : Finset (V → Bool)).filter goodSpin,
          if ∀ i ∈ P, x (some (i, false)) = false then
            ∏ i : T, weight (1, i) (xor (x none) (x (some (i, false))))
          else 0 := by
      rw [← Finset.sum_subset (Finset.filter_subset goodSpin Finset.univ)]
      · refine Finset.sum_congr rfl (fun x hx => ?_)
        have hgx : goodSpin x := (Finset.mem_filter.mp hx).2
        rw [hdiff_good x hgx, hprod_good x hgx]
        simp
      · intro x _ hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        split_ifs
        · exact hzero_bad x hnot
        · rfl
    rw [hsum_good]
    let mkX : Bool × (T → Bool) → (V → Bool) := fun hb v =>
      match v with
      | none => hb.1
      | some (i, false) => hb.2 i
      | some (i, true) => !(hb.2 i)
    have hbij_sum : (∑ x ∈ (Finset.univ : Finset (V → Bool)).filter goodSpin,
          if ∀ i ∈ P, x (some (i, false)) = false then
            ∏ i : T, weight (1, i) (xor (x none) (x (some (i, false))))
          else 0) =
        ∑ hb : Bool × (T → Bool),
          if ∀ i ∈ P, hb.2 i = false then
            ∏ i : T, weight (1, i) (xor hb.1 (hb.2 i))
          else 0 := by
      symm
      refine Finset.sum_bij (fun hb _ => mkX hb) ?_ ?_ ?_ ?_
      · intro hb _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, goodSpin, mkX]
        intro _; trivial
      · intro hb1 _ hb2 _ heq
        apply Prod.ext
        · exact congrFun heq none
        · funext i; exact congrFun heq (some (i, false))
      · intro x hx
        have hgx : goodSpin x := (Finset.mem_filter.mp hx).2
        refine ⟨(x none, fun i => x (some (i, false))), Finset.mem_univ _, ?_⟩
        funext v
        rcases v with _ | ⟨i, b⟩
        · rfl
        · cases b
          · rfl
          · exact (hgx i).symm
      · intro hb _
        rfl
    rw [hbij_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    have hinner : (∑ b : T → Bool, if ∀ i ∈ P, b i = false then
          ∏ i : T, weight (1, i) (xor h (b i)) else 0) =
        ∑ b : T → Bool, ∏ i : T, (if i ∈ P ∧ b i = true then 0 else weight (1, i) (xor h (b i))) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hP : ∀ i ∈ P, b i = false
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        have hnot : ¬ (i ∈ P ∧ b i = true) := by
          rintro ⟨hiP, hbt⟩
          have := hP i hiP
          rw [hbt] at this; exact Bool.noConfusion this
        simp [hnot]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
        push Not at hP
        rcases hP with ⟨i0, hi0P, hi0ne⟩
        have hi0t : b i0 = true := Bool.eq_true_of_not_eq_false hi0ne
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
        simp [hi0P, hi0t]
    rw [hinner]
    rw [← Fintype.prod_sum (fun (i : T) (bit : Bool) => if i ∈ P ∧ bit = true then 0 else weight (1, i) (xor h bit))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_bool]
    have h10 : ((1 : Fin 3) ≠ 0) := by decide
    have h12 : ((1 : Fin 3) ≠ 2) := by decide
    by_cases hiP : i ∈ P
    · simp only [hiP, true_and, ↓reduceIte, zero_add, Bool.xor_false]
      dsimp only [weight]
      simp [h10, h12]
    · simp only [hiP, false_and, ↓reduceIte]
      dsimp only [weight]
      simp only [h10, h12, ↓reduceIte]
      cases g.elim false (fun p => decide (p.val.1 = i ∨ p.val.2 = i)) <;> cases h <;> decide
  · simp only [hl, ↓reduceIte]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs with hc
    · by_cases hgx : goodSpin x
      · exact absurd (hc.2.symm.trans (hdiff_good x hgx)) hl
      · have hterm := hzero_bad x hgx
        dsimp only [weight, tail, head] at hterm
        refine Eq.trans (Finset.prod_congr rfl (fun e _ => ?_)) hterm
        split_ifs <;> rfl
    · rfl

private lemma inj_hit_count {α : Type*} [Fintype α] [DecidableEq α] (q : ℕ)
    (_hq : q ≤ Fintype.card α) (p0 : α) :
    let Inj := {f : Fin q → α // Function.Injective f}
    Fintype.card α * ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p0)).card =
      q * Fintype.card Inj := by
  classical
  dsimp only
  let Inj := {f : Fin q → α // Function.Injective f}
  have hsame : ∀ p1 p2 : α,
      ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p1)).card =
      ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p2)).card := by
    intro p1 p2
    let sw := Equiv.swap p1 p2
    refine Finset.card_bij (fun f _ => ⟨sw ∘ f.1, sw.injective.comp f.2⟩) ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      rcases hf with ⟨i, hi⟩
      exact ⟨i, by simp [sw, hi]⟩
    · intro f1 _ f2 _ heq
      apply Subtype.ext
      funext i
      have h1 := congrFun (congrArg Subtype.val heq) i
      exact sw.injective h1
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rcases hf with ⟨i, hi⟩
      refine ⟨⟨sw ∘ f.1, sw.injective.comp f.2⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, by simp [sw, hi]⟩
      · apply Subtype.ext; funext j; simp [sw]
  have hdouble : ∑ p : α, ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p)).card =
      q * Fintype.card Inj := by
    calc ∑ p : α, ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p)).card
        = ∑ p : α, ∑ f : Inj, if ∃ i : Fin q, f.1 i = p then 1 else 0 := by
            refine Finset.sum_congr rfl (fun p _ => by simp)
      _ = ∑ f : Inj, ∑ p : α, if ∃ i : Fin q, f.1 i = p then 1 else 0 := Finset.sum_comm
      _ = ∑ f : Inj, (Finset.univ.image f.1).card := by
            refine Finset.sum_congr rfl (fun f _ => ?_)
            have h1 : (Finset.univ.image f.1).card =
                ((Finset.univ : Finset α).filter (fun p => ∃ i : Fin q, f.1 i = p)).card := by
              congr 1; ext p; simp
            rw [h1]; simp
      _ = ∑ _f : Inj, q := by
            refine Finset.sum_congr rfl (fun f _ => ?_)
            rw [Finset.card_image_of_injective _ f.2, Finset.card_univ, Fintype.card_fin]
      _ = q * Fintype.card Inj := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hconst : ∑ p : α, ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p)).card =
      Fintype.card α * ((Finset.univ : Finset Inj).filter (fun f => ∃ i : Fin q, f.1 i = p0)).card := by
    rw [Finset.sum_congr rfl (fun p _ => hsame p p0), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← hconst, hdouble]

private lemma inj_nonempty {α : Type*} [Fintype α] (q : ℕ) (hq : q ≤ Fintype.card α) :
    Nonempty {f : Fin q → α // Function.Injective f} := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  refine ⟨⟨fun i => e ⟨i.val, lt_of_lt_of_le i.isLt hq⟩, ?_⟩⟩
  intro i1 i2 heq
  have h := e.injective heq
  exact Fin.ext (by simpa using congrArg Fin.val h)

end PEqualNP.Outside.L_pcx_447_aux

open PEqualNP.Outside.L_pcx_447_aux

theorem PEqualNP.Outside.L_pcx_447 :
    (∀ t : ℕ, 2 ≤ t →
  let T := Fin t
  let V := Option (T × Bool)
  let Pair := {p : T × T // p.1 < p.2}
  let N := t.choose 2
  let E := Fin 3 × T
  let tail := fun e : E => if e.1 = 0 then some (e.2,false) else (none : V)
  let head := fun e : E => some (e.2,decide (e.1 ≠ 1))
  let weight := fun (g : Option Pair) (e : E) (diff : Bool) =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let obs := fun (g : Option Pair) (P : Finset T) (l : ℕ) =>
    ∑ x : V → Bool, if (∀ i ∈ P, x (some (i,false)) = false) ∧
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = l then
        ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0
  let pairPins := fun p : Pair => ({p.val.1,p.val.2} : Finset T)
  (∀ (g : Option Pair) (P : Finset T) (l : ℕ), l ≠ 2*t → obs g P l = 0) ∧
  (∀ g, obs g ∅ (2*t) = 2*4^t) ∧
  (∀ (g : Option Pair) (p : Pair), obs g (pairPins p) (2*t) =
    (if g = some p then 10 else 8)*4^(t-2)) ∧
  (∀ g, obs g Finset.univ (2*t) = (if g.isSome then 10 else 8)*2^(t-2)) ∧
  ∀ (q num den : ℕ), q ≤ N → 0 < den →
    ((∃ (R : ℕ), 0 < R ∧
      ∃ (ask : Fin R → (i : Fin q) → (Fin i.val → ℕ) → Pair)
        (answer : Fin R → (Fin q → ℕ) → Bool)
        (run : Option Pair → Fin R → Fin q → ℕ),
        (∀ g seed i, run g seed i = obs g
          (pairPins (ask seed i (fun j => run g seed (j.castLE (Nat.le_of_lt i.isLt))))) (2*t)) ∧
        ∀ g, num*R ≤ den*((Finset.univ : Finset (Fin R)).filter (fun seed =>
          answer seed (run g seed) = decide (obs g Finset.univ (2*t) ≠ obs none Finset.univ (2*t)))).card) ↔
      num*(2*N-q) ≤ den*N)) := by
  intro t ht
  dsimp only
  let T := Fin t
  let V := Option (T × Bool)
  let Pair := {p : T × T // p.1 < p.2}
  let N := t.choose 2
  let E := Fin 3 × T
  let tail : E → V := fun e => if e.1 = 0 then some (e.2, false) else none
  let head : E → V := fun e => some (e.2, decide (e.1 ≠ 1))
  let weight : Option Pair → E → Bool → ℕ := fun g e diff =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let obs : Option Pair → Finset T → ℕ → ℕ := fun g P l =>
    ∑ x : V → Bool, if (∀ i ∈ P, x (some (i, false)) = false) ∧
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = l then
        ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0
  let pairPins : Pair → Finset T := fun p => ({p.val.1, p.val.2} : Finset T)
  have hcardPair : Fintype.card Pair = N := card_pair_eq_choose t
  have hN_pos : 0 < N := by
    have : 2 ≤ t := ht
    have h1 : 0 < t.choose 2 := Nat.choose_pos this
    exact h1
  have hobs1 : ∀ (g : Option Pair) (P : Finset T) (l : ℕ), l ≠ 2 * t → obs g P l = 0 := by
    intro g P l hl
    have hf := obs_formula g P l
    dsimp only at hf
    change obs g P l = _ at hf
    rw [hf]
    simp only [hl, ↓reduceIte]
  have hobs2 : ∀ g : Option Pair, obs g ∅ (2 * t) = 2 * 4 ^ t := by
    intro g
    have hf := obs_formula g ∅ (2 * t)
    dsimp only at hf
    change obs g ∅ (2 * t) = _ at hf
    rw [hf]
    simp [two_mul]
  have hobs3 : ∀ (g : Option Pair) (p : Pair),
      obs g (pairPins p) (2 * t) = (if g = some p then 10 else 8) * 4 ^ (t - 2) := by
    intro g p
    have hf := obs_formula g (pairPins p) (2 * t)
    dsimp only at hf
    change obs g (pairPins p) (2 * t) = _ at hf
    rw [hf]
    simp only [↓reduceIte, Fintype.sum_bool]
    have hsplit : ∀ h : Bool,
        (∏ i : T, if i ∈ pairPins p then weight g (1, i) (xor h false) else 4) =
        weight g (1, p.val.1) (xor h false) * weight g (1, p.val.2) (xor h false) * 4 ^ (t - 2) := by
      intro h
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : T => i ∈ pairPins p)]
      have h1 : Finset.univ.filter (fun i : T => i ∈ pairPins p) = {p.val.1, p.val.2} := by
        ext i; simp [pairPins]
      have h2 : (Finset.univ.filter (fun i : T => i ∉ pairPins p)).card = t - 2 := by
        have hcomp : Finset.univ.filter (fun i : T => i ∉ pairPins p) = Finset.univ \ pairPins p := by
          ext i; simp
        rw [hcomp, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
        dsimp only [pairPins]
        rw [Finset.card_pair (ne_of_lt p.2)]
      have hp1 : (∏ i ∈ Finset.univ.filter (fun i : T => i ∈ pairPins p),
            if i ∈ pairPins p then weight g (1, i) (xor h false) else 4) =
          weight g (1, p.val.1) (xor h false) * weight g (1, p.val.2) (xor h false) := by
        rw [h1, Finset.prod_pair (ne_of_lt p.2)]
        simp [pairPins]
      have hp2 : (∏ i ∈ Finset.univ.filter (fun i : T => i ∉ pairPins p),
            if i ∈ pairPins p then weight g (1, i) (xor h false) else 4) = 4 ^ (t - 2) := by
        have hall : ∀ i ∈ Finset.univ.filter (fun i : T => i ∉ pairPins p),
            (if i ∈ pairPins p then weight g (1, i) (xor h false) else 4) = 4 := by
          intro i hi; simp [(Finset.mem_filter.mp hi).2]
        rw [Finset.prod_congr rfl hall, Finset.prod_const, h2]
      rw [hp1, hp2]
    rw [hsplit true, hsplit false, ← add_mul]
    congr 1
    have h10 : ((1 : Fin 3) ≠ 0) := by decide
    have h12 : ((1 : Fin 3) ≠ 2) := by decide
    dsimp only [weight]
    simp only [h10, h12, ↓reduceIte, Bool.xor_false]
    cases g with
    | none => simp
    | some q =>
      by_cases hqp : q = p
      · subst hqp
        simp
      · have hnotboth : ¬ ((q.val.1 = p.val.1 ∨ q.val.2 = p.val.1) ∧ (q.val.1 = p.val.2 ∨ q.val.2 = p.val.2)) := by
          rintro ⟨h1, h2⟩
          apply hqp
          apply Subtype.ext
          have hltp := p.2
          have hltq := q.2
          rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
          · exact absurd (h1a.symm.trans h2a) (ne_of_lt hltp)
          · exact Prod.ext h1a h2b
          · exfalso; rw [h1b, h2a] at hltq; exact absurd hltq (not_lt.mpr (le_of_lt hltp))
          · exact absurd (h1b.symm.trans h2b) (ne_of_lt hltp)
        have hne : some q ≠ some p := fun h => hqp (Option.some.inj h)
        simp only [hne, ↓reduceIte, Option.elim_some]
        by_cases ha : q.val.1 = p.val.1 ∨ q.val.2 = p.val.1 <;>
        by_cases hb : q.val.1 = p.val.2 ∨ q.val.2 = p.val.2
        · exact absurd ⟨ha, hb⟩ hnotboth
        · simp [ha, hb]
        · simp [ha, hb]
        · simp [ha, hb]
  have hobs4 : ∀ g : Option Pair,
      obs g Finset.univ (2 * t) = (if g.isSome then 10 else 8) * 2 ^ (t - 2) := by
    intro g
    have hf := obs_formula g Finset.univ (2 * t)
    dsimp only at hf
    change obs g Finset.univ (2 * t) = _ at hf
    rw [hf]
    simp only [↓reduceIte, Finset.mem_univ, Fintype.sum_bool]
    have h10 : ((1 : Fin 3) ≠ 0) := by decide
    have h12 : ((1 : Fin 3) ≠ 2) := by decide
    cases g with
    | none =>
      have hw : ∀ h : Bool, ∀ i : T, weight none (1, i) (xor h false) = 2 := by
        intro h i; dsimp only [weight]; simp [h10, h12]
      change (∏ i : T, weight none (1, i) (xor true false)) +
        (∏ i : T, weight none (1, i) (xor false false)) = _
      rw [Finset.prod_congr rfl (fun i _ => hw true i), Finset.prod_congr rfl (fun i _ => hw false i),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have ht2 : t = (t - 2) + 2 := by omega
      conv_lhs => rw [ht2]
      ring
    | some p =>
      have hsplit : ∀ h : Bool,
          (∏ i : T, weight (some p) (1, i) (xor h false)) =
          weight (some p) (1, p.val.1) (xor h false) * weight (some p) (1, p.val.2) (xor h false) * 2 ^ (t - 2) := by
        intro h
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : T => i ∈ pairPins p)]
        have h1 : Finset.univ.filter (fun i : T => i ∈ pairPins p) = {p.val.1, p.val.2} := by
          ext i; simp [pairPins]
        have h2 : (Finset.univ.filter (fun i : T => i ∉ pairPins p)).card = t - 2 := by
          have hcomp : Finset.univ.filter (fun i : T => i ∉ pairPins p) = Finset.univ \ pairPins p := by
            ext i; simp
          rw [hcomp, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
            Fintype.card_fin]
          dsimp only [pairPins]
          rw [Finset.card_pair (ne_of_lt p.2)]
        have hp1 : (∏ i ∈ Finset.univ.filter (fun i : T => i ∈ pairPins p),
              weight (some p) (1, i) (xor h false)) =
            weight (some p) (1, p.val.1) (xor h false) * weight (some p) (1, p.val.2) (xor h false) := by
          rw [h1, Finset.prod_pair (ne_of_lt p.2)]
        have hp2 : (∏ i ∈ Finset.univ.filter (fun i : T => i ∉ pairPins p),
              weight (some p) (1, i) (xor h false)) = 2 ^ (t - 2) := by
          have hall : ∀ i ∈ Finset.univ.filter (fun i : T => i ∉ pairPins p),
              weight (some p) (1, i) (xor h false) = 2 := by
            intro i hi
            have hni : i ∉ pairPins p := (Finset.mem_filter.mp hi).2
            simp only [pairPins, Finset.mem_insert, Finset.mem_singleton, not_or] at hni
            dsimp only [weight]
            simp [h10, h12, Ne.symm hni.1, Ne.symm hni.2]
          rw [Finset.prod_congr rfl hall, Finset.prod_const, h2]
        rw [hp1, hp2]
      rw [hsplit true, hsplit false, ← add_mul]
      simp only [Option.isSome_some, ↓reduceIte]
      congr 1
      dsimp only [weight]
      simp [h10, h12]
  have htarget_iff : ∀ g : Option Pair,
      decide (obs g Finset.univ (2 * t) ≠ obs none Finset.univ (2 * t)) = g.isSome := by
    intro g
    rw [hobs4 g, hobs4 none]
    cases g with
    | none => simp
    | some p =>
      simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        decide_eq_true_eq]
      have hpos : 0 < 2 ^ (t - 2) := Nat.two_pow_pos _
      omega
  refine ⟨hobs1, hobs2, hobs3, hobs4, ?_⟩
  intro q num den hqN hden
  constructor
  · rintro ⟨R, hR, ask, answer, run, hrun, hacc⟩
    change ∀ g seed i, run g seed i = obs g
      (pairPins (ask seed i (fun j => run g seed (j.castLE (Nat.le_of_lt i.isLt))))) (2 * t) at hrun
    change ∀ g, num * R ≤ den * ((Finset.univ : Finset (Fin R)).filter (fun seed =>
      answer seed (run g seed) = decide (obs g Finset.univ (2 * t) ≠ obs none Finset.univ (2 * t)))).card at hacc
    let Q : Fin R → Finset Pair := fun seed =>
      Finset.univ.image (fun i : Fin q =>
        ask seed i (fun j => run none seed (j.castLE (Nat.le_of_lt i.isLt))))
    have hQ_card : ∀ seed : Fin R, (Q seed).card ≤ q := by
      intro seed
      calc (Q seed).card ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
        _ = q := Fintype.card_fin q
    have hrun_agree : ∀ (seed : Fin R) (p : Pair), p ∉ Q seed → run (some p) seed = run none seed := by
      intro seed p hpnot
      have hind : ∀ (m : ℕ) (hm : m < q), run (some p) seed ⟨m, hm⟩ = run none seed ⟨m, hm⟩ := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          intro hm
          rw [hrun (some p) seed ⟨m, hm⟩, hrun none seed ⟨m, hm⟩]
          have hhist : (fun j : Fin m => run (some p) seed (j.castLE (Nat.le_of_lt hm))) =
              (fun j : Fin m => run none seed (j.castLE (Nat.le_of_lt hm))) := by
            funext j
            exact ih j.val j.isLt (lt_trans j.isLt hm)
          rw [hhist]
          let curP := ask seed ⟨m, hm⟩ (fun j => run none seed (j.castLE (Nat.le_of_lt hm)))
          have hcur_mem : curP ∈ Q seed :=
            Finset.mem_image_of_mem _ (Finset.mem_univ (⟨m, hm⟩ : Fin q))
          have hne : curP ≠ p := fun heq => hpnot (heq ▸ hcur_mem)
          rw [hobs3 (some p) curP, hobs3 none curP]
          have hne_opt : some p ≠ some curP := fun h => hne (Option.some.inj h).symm
          simp [hne_opt]
      funext i
      exact hind i.val i.isLt
    let Afalse : Finset (Fin R) := Finset.univ.filter (fun seed => answer seed (run none seed) = false)
    have hnone_bound : num * R ≤ den * Afalse.card := by
      have h0 := hacc none
      simp only [htarget_iff none, Option.isSome_none] at h0
      exact h0
    have hsum_some : N * (num * R) ≤ den * ((R - Afalse.card) * N + Afalse.card * q) := by
      have h1 : N * (num * R) ≤
          ∑ p : Pair, den * ((Finset.univ : Finset (Fin R)).filter (fun seed => answer seed (run (some p) seed) = true)).card := by
        calc N * (num * R)
            = ∑ _p : Pair, num * R := by rw [Finset.sum_const, Finset.card_univ, hcardPair, smul_eq_mul]
          _ ≤ ∑ p : Pair, den * ((Finset.univ : Finset (Fin R)).filter (fun seed => answer seed (run (some p) seed) = true)).card := by
              refine Finset.sum_le_sum (fun p _ => ?_)
              have hp := hacc (some p)
              simp only [htarget_iff (some p), Option.isSome_some] at hp
              exact hp
      have hswap : (∑ p : Pair, ((Finset.univ : Finset (Fin R)).filter (fun seed => answer seed (run (some p) seed) = true)).card) =
          ∑ seed : Fin R, ((Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true)).card := by
        calc ∑ p : Pair, ((Finset.univ : Finset (Fin R)).filter (fun seed => answer seed (run (some p) seed) = true)).card
            = ∑ p : Pair, ∑ seed : Fin R, if answer seed (run (some p) seed) = true then 1 else 0 := by
                refine Finset.sum_congr rfl (fun p _ => by simp)
          _ = ∑ seed : Fin R, ∑ p : Pair, if answer seed (run (some p) seed) = true then 1 else 0 := Finset.sum_comm
          _ = ∑ seed : Fin R, ((Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true)).card := by
                refine Finset.sum_congr rfl (fun seed _ => by rw [Finset.card_filter])
      have hseed_bound : ∀ seed : Fin R,
          ((Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true)).card ≤
          if seed ∈ Afalse then q else N := by
        intro seed
        by_cases hsf : seed ∈ Afalse
        · simp only [hsf, ↓reduceIte]
          have hsub : (Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true) ⊆ Q seed := by
            intro p hp
            by_contra hpnot
            have h1 := (Finset.mem_filter.mp hp).2
            rw [hrun_agree seed p hpnot] at h1
            have h2 := (Finset.mem_filter.mp hsf).2
            rw [h2] at h1
            exact Bool.noConfusion h1
          exact le_trans (Finset.card_le_card hsub) (hQ_card seed)
        · simp only [hsf, ↓reduceIte]
          calc ((Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true)).card
              ≤ (Finset.univ : Finset Pair).card := Finset.card_le_univ _
            _ = N := hcardPair
      have hsum_le : (∑ seed : Fin R, ((Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true)).card) ≤
          (R - Afalse.card) * N + Afalse.card * q := by
        calc (∑ seed : Fin R, ((Finset.univ : Finset Pair).filter (fun p => answer seed (run (some p) seed) = true)).card)
            ≤ ∑ seed : Fin R, if seed ∈ Afalse then q else N := Finset.sum_le_sum (fun seed _ => hseed_bound seed)
          _ = Afalse.card * q + (R - Afalse.card) * N := by
              rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
              have h1 : (Finset.univ.filter (fun seed : Fin R => seed ∈ Afalse)).card = Afalse.card := by
                congr 1; ext s; simp
              have h2 : (Finset.univ.filter (fun seed : Fin R => seed ∉ Afalse)).card = R - Afalse.card := by
                have hc : Finset.univ.filter (fun seed : Fin R => seed ∉ Afalse) = Finset.univ \ Afalse := by
                  ext s; simp
                rw [hc, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
              rw [h1, h2]
          _ = (R - Afalse.card) * N + Afalse.card * q := add_comm _ _
      rw [← Finset.mul_sum, hswap] at h1
      exact le_trans h1 (Nat.mul_le_mul_left den hsum_le)
    have hA_le_R : Afalse.card ≤ R := by
      calc Afalse.card ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_univ _
        _ = R := Fintype.card_fin R
    have hcomb : (2 * N - q) * (num * R) ≤ den * (N * R) := by
      have h2 := Nat.mul_le_mul_left (N - q) hnone_bound
      have hadd := Nat.add_le_add hsum_some h2
      have hlhs : N * (num * R) + (N - q) * (num * R) = (2 * N - q) * (num * R) := by
        rw [← add_mul]
        congr 1
        omega
      have hrhs : den * ((R - Afalse.card) * N + Afalse.card * q) + (N - q) * (den * Afalse.card) =
          den * (N * R) := by
        have hRN : (R - Afalse.card) * N + Afalse.card * N = R * N := by
          rw [← add_mul, Nat.sub_add_cancel hA_le_R]
        have hNq : Afalse.card * q + Afalse.card * (N - q) = Afalse.card * N := by
          rw [← mul_add, Nat.add_sub_of_le hqN]
        calc den * ((R - Afalse.card) * N + Afalse.card * q) + (N - q) * (den * Afalse.card)
            = den * ((R - Afalse.card) * N + (Afalse.card * q + Afalse.card * (N - q))) := by ring
          _ = den * ((R - Afalse.card) * N + Afalse.card * N) := by rw [hNq]
          _ = den * (R * N) := by rw [hRN]
          _ = den * (N * R) := by ring
      rw [hlhs, hrhs] at hadd
      exact hadd
    have hmul : num * (2 * N - q) * R ≤ den * N * R := by
      calc num * (2 * N - q) * R = (2 * N - q) * (num * R) := by ring
        _ ≤ den * (N * R) := hcomb
        _ = den * N * R := by ring
    exact Nat.le_of_mul_le_mul_right hmul hR
  · intro hineq
    classical
    let Inj := {f : Fin q → Pair // Function.Injective f}
    have hInj_ne : Nonempty Inj := inj_nonempty q (by rw [hcardPair]; exact hqN)
    have hInj_pos : 0 < Fintype.card Inj := Fintype.card_pos_iff.mpr hInj_ne
    have h2Nq_pos : 0 < 2 * N - q := by omega
    let Seed := Inj × Fin (2 * N - q)
    let R := Fintype.card Seed
    have hR_eq : R = Fintype.card Inj * (2 * N - q) := by
      dsimp only [R, Seed]
      rw [Fintype.card_prod, Fintype.card_fin]
    have hR_pos : 0 < R := by rw [hR_eq]; exact Nat.mul_pos hInj_pos h2Nq_pos
    let eSeed : Fin R ≃ Seed := (Fintype.equivFin Seed).symm
    let ask : Fin R → (i : Fin q) → (Fin i.val → ℕ) → Pair := fun seed i _ => (eSeed seed).1.1 i
    let run : Option Pair → Fin R → Fin q → ℕ := fun g seed i => obs g (pairPins ((eSeed seed).1.1 i)) (2 * t)
    let answer : Fin R → (Fin q → ℕ) → Bool := fun seed hist =>
      if ∃ i : Fin q, hist i = 10 * 4 ^ (t - 2) then true
      else decide ((eSeed seed).2.val < N - q)
    refine ⟨R, hR_pos, ask, answer, run, fun g seed i => rfl, ?_⟩
    intro g
    have hpow_pos : 0 < 4 ^ (t - 2) := Nat.pow_pos (by omega)
    have h8_ne_10 : 8 * 4 ^ (t - 2) ≠ 10 * 4 ^ (t - 2) := by omega
    have hsucc_eq : ((Finset.univ : Finset (Fin R)).filter (fun seed =>
        answer seed (run g seed) = decide (obs g Finset.univ (2 * t) ≠ obs none Finset.univ (2 * t)))).card =
        Fintype.card Inj * N := by
      have hbij : ((Finset.univ : Finset (Fin R)).filter (fun seed =>
            answer seed (run g seed) = decide (obs g Finset.univ (2 * t) ≠ obs none Finset.univ (2 * t)))).card =
          ((Finset.univ : Finset Seed).filter (fun s =>
            (if ∃ i : Fin q, obs g (pairPins (s.1.1 i)) (2 * t) = 10 * 4 ^ (t - 2) then true
             else decide (s.2.val < N - q)) = g.isSome)).card := by
        refine Finset.card_bij (fun seed _ => eSeed seed) ?_ ?_ ?_
        · intro seed hseed
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htarget_iff g] at hseed ⊢
          exact hseed
        · intro s1 _ s2 _ heq; exact eSeed.injective heq
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          refine ⟨eSeed.symm s, ?_, eSeed.apply_symm_apply s⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, htarget_iff g, answer, run,
            eSeed.apply_symm_apply]
          exact hs
      rw [hbij]
      cases g with
      | none =>
        have hnohit : ∀ s : Seed, ¬ ∃ i : Fin q, obs none (pairPins (s.1.1 i)) (2 * t) = 10 * 4 ^ (t - 2) := by
          intro s; rintro ⟨i, hi⟩
          rw [hobs3 none (s.1.1 i)] at hi
          simp only [reduceCtorEq, ↓reduceIte] at hi
          exact h8_ne_10 hi
        have hfilt : (Finset.univ : Finset Seed).filter (fun s =>
            (if ∃ i : Fin q, obs none (pairPins (s.1.1 i)) (2 * t) = 10 * 4 ^ (t - 2) then true
             else decide (s.2.val < N - q)) = false) =
            (Finset.univ : Finset Inj) ×ˢ (Finset.univ.filter (fun c : Fin (2 * N - q) => ¬ c.val < N - q)) := by
          ext ⟨f, c⟩
          rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
          simp only [Finset.mem_univ, true_and, hnohit (f, c), ↓reduceIte, decide_eq_false_iff_not]
        simp only [Option.isSome_none]
        rw [hfilt, Finset.card_product, Finset.card_univ]
        congr 1
        have hbijC : ((Finset.univ : Finset (Fin (2 * N - q))).filter (fun c => ¬ c.val < N - q)).card =
            (Finset.univ : Finset (Fin N)).card := by
          refine Finset.card_bij (fun c hc => ⟨c.val - (N - q), by
            have := (Finset.mem_filter.mp hc).2
            have := c.isLt
            omega⟩) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro c1 hc1 c2 hc2 heq
            have h1 := (Finset.mem_filter.mp hc1).2
            have h2 := (Finset.mem_filter.mp hc2).2
            have hv := congrArg Fin.val heq
            dsimp only at hv
            exact Fin.ext (by omega)
          · intro j _
            refine ⟨⟨N - q + j.val, by have := j.isLt; omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
            simp; omega
        rw [hbijC, Finset.card_univ, Fintype.card_fin]
      | some p =>
        have hhit_iff : ∀ f : Inj,
            (∃ i : Fin q, obs (some p) (pairPins (f.1 i)) (2 * t) = 10 * 4 ^ (t - 2)) ↔
            (∃ i : Fin q, f.1 i = p) := by
          intro f
          refine exists_congr (fun i => ?_)
          rw [hobs3 (some p) (f.1 i)]
          by_cases hfp : f.1 i = p
          · simp [hfp]
          · have hne : some p ≠ some (f.1 i) := fun h => hfp (Option.some.inj h).symm
            simp [hne, hfp, h8_ne_10]
        let Hit : Finset Inj := Finset.univ.filter (fun f => ∃ i : Fin q, f.1 i = p)
        let Miss : Finset Inj := Finset.univ.filter (fun f => ¬ ∃ i : Fin q, f.1 i = p)
        have hfib : ((Finset.univ : Finset Seed).filter (fun s =>
            (if ∃ i : Fin q, obs (some p) (pairPins (s.1.1 i)) (2 * t) = 10 * 4 ^ (t - 2) then true
             else decide (s.2.val < N - q)) = true)).card =
            Hit.card * (2 * N - q) + Miss.card * (N - q) := by
          rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
          have hper : ∀ f : Inj,
              (((Finset.univ : Finset Seed).filter (fun s =>
                (if ∃ i : Fin q, obs (some p) (pairPins (s.1.1 i)) (2 * t) = 10 * 4 ^ (t - 2) then true
                 else decide (s.2.val < N - q)) = true)).filter (fun s => s.1 = f)).card =
              if f ∈ Hit then 2 * N - q else N - q := by
            intro f
            have hbijF : (((Finset.univ : Finset Seed).filter (fun s =>
                  (if ∃ i : Fin q, obs (some p) (pairPins (s.1.1 i)) (2 * t) = 10 * 4 ^ (t - 2) then true
                   else decide (s.2.val < N - q)) = true)).filter (fun s => s.1 = f)).card =
                ((Finset.univ : Finset (Fin (2 * N - q))).filter (fun c =>
                  (if ∃ i : Fin q, f.1 i = p then true else decide (c.val < N - q)) = true)).card := by
              refine Finset.card_bij (fun s _ => s.2) ?_ ?_ ?_
              · intro s hs
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
                rcases hs with ⟨h1, rfl⟩
                simpa only [hhit_iff] using h1
              · intro s1 hs1 s2 hs2 heq
                simp only [Finset.mem_filter] at hs1 hs2
                exact Prod.ext (hs1.2.trans hs2.2.symm) heq
              · intro c hc
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
                refine ⟨(f, c), ?_, rfl⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, hhit_iff]
                exact ⟨hc, trivial⟩
            rw [hbijF]
            by_cases hf : f ∈ Hit
            · have hf' : ∃ i : Fin q, f.1 i = p := (Finset.mem_filter.mp hf).2
              simp [hf, hf']
            · have hf' : ¬ ∃ i : Fin q, f.1 i = p := by simpa [Hit] using hf
              simp only [hf, hf', ↓reduceIte, decide_eq_true_eq]
              have hbijM : ((Finset.univ : Finset (Fin (2 * N - q))).filter (fun c => c.val < N - q)).card =
                  (Finset.univ : Finset (Fin (N - q))).card := by
                refine Finset.card_bij (fun c hc => ⟨c.val, (Finset.mem_filter.mp hc).2⟩) ?_ ?_ ?_
                · intro _ _; exact Finset.mem_univ _
                · intro c1 _ c2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
                · intro j _
                  refine ⟨⟨j.val, by have := j.isLt; omega⟩, ?_, Fin.ext rfl⟩
                  simp [j.isLt]
              rw [hbijM, Finset.card_univ, Fintype.card_fin]
          rw [Finset.sum_congr rfl (fun f _ => hper f), Finset.sum_ite, Finset.sum_const,
            Finset.sum_const, smul_eq_mul, smul_eq_mul]
          congr 1
          · congr 2; ext f; simp [Hit]
          · congr 2; ext f; simp [Hit, Miss]
        simp only [Option.isSome_some]
        rw [hfib]
        have hHit_eq : N * Hit.card = q * Fintype.card Inj := by
          have := inj_hit_count q (by rw [hcardPair]; exact hqN) p
          rwa [hcardPair] at this
        have hsum_HM : Hit.card + Miss.card = Fintype.card Inj := by
          have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Inj))
            (p := fun f => ∃ i : Fin q, f.1 i = p)
          simpa [Hit, Miss] using h1
        have hmulN : Hit.card * (2 * N - q) + Miss.card * (N - q) = Fintype.card Inj * N := by
          have h1 : 2 * N - q = N + (N - q) := by omega
          rw [h1, mul_add]
          calc Hit.card * N + Hit.card * (N - q) + Miss.card * (N - q)
              = N * Hit.card + (Hit.card + Miss.card) * (N - q) := by ring
            _ = q * Fintype.card Inj + Fintype.card Inj * (N - q) := by rw [hHit_eq, hsum_HM]
            _ = Fintype.card Inj * (q + (N - q)) := by ring
            _ = Fintype.card Inj * N := by rw [Nat.add_sub_of_le hqN]
        exact hmulN
    rw [hsucc_eq, hR_eq]
    calc num * (Fintype.card Inj * (2 * N - q))
        = Fintype.card Inj * (num * (2 * N - q)) := by ring
      _ ≤ Fintype.card Inj * (den * N) := Nat.mul_le_mul_left _ hineq
      _ = den * (Fintype.card Inj * N) := by ring

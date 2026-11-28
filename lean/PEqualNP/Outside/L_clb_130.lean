import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_130

open PEqualNP.MetaComplexity

def addr (r a b : ℕ) : Fin 12 := Fin.ofNat 12 (4 * r + a + 2 * b)

def walk (x : Fin 12 → Bool) : Bool :=
  decide (∃ s t u : Fin 2, x (addr 0 s.val t.val) = true ∧
    x (addr 1 t.val u.val) = true ∧ x (addr 2 u.val s.val) = true)

def occ {n : ℕ} : DMFormula n → Fin n → ℕ
  | .lit j _, i => if j = i then 1 else 0
  | .and A B, i => occ A i + occ B i
  | .or A B, i => occ A i + occ B i

theorem leaves_eq {n : ℕ} (F : DMFormula n) : F.leaves = ∑ i, occ F i := by
  induction F with
  | lit j b => simp [DMFormula.leaves, occ]
  | and A B ha hb => simp [DMFormula.leaves, occ, Finset.sum_add_distrib, ha, hb]
  | or A B ha hb => simp [DMFormula.leaves, occ, Finset.sum_add_distrib, ha, hb]

def score (a ap aq b bp bq : Bool) : ℕ :=
  ((a != ap) || (b != bp)).toNat + ((a != aq) || (b != bq)).toNat +
    ((a != b) && (a != ap) && (a != aq) && (b != bp) && (b != bq)).toNat

theorem score_neg : ∀ a ap aq b bp bq : Bool,
    score (!a) (!ap) (!aq) (!b) (!bp) (!bq) = score a ap aq b bp bq := by
  decide

theorem score_and : ∀ a ap aq b bp bq c cp cq d dp dq : Bool,
    score (a && c) (ap && cp) (aq && cq) (b && d) (bp && dp) (bq && dq) ≤
      score a ap aq b bp bq + score c cp cq d dp dq := by
  decide +kernel

theorem score_or : ∀ a ap aq b bp bq c cp cq d dp dq : Bool,
    score (a || c) (ap || cp) (aq || cq) (b || d) (bp || dp) (bq || dq) ≤
      score a ap aq b bp bq + score c cp cq d dp dq := by
  decide +kernel

structure Samples (α : Type) where
  hi : α
  hp : α
  hq : α
  lo : α
  lp : α
  lq : α

def weight {α : Type} (S : Samples α) (f : α → Bool) : ℕ :=
  score (f S.hi) (f S.hp) (f S.hq) (f S.lo) (f S.lp) (f S.lq)

theorem weight_le {n : ℕ} (S : Samples (Fin n → Bool)) (p q : Fin n)
    (h : ∀ i, weight S (fun x => x i) ≤
      (if i = p then 1 else 0) + (if i = q then 1 else 0)) (F : DMFormula n) :
    weight S F.eval ≤ occ F p + occ F q := by
  induction F with
  | lit i b =>
    cases b
    · change score (!(S.hi i)) (!(S.hp i)) (!(S.hq i)) (!(S.lo i)) (!(S.lp i)) (!(S.lq i)) ≤ _
      rw [score_neg]
      exact h i
    · exact h i
  | and A B ha hb =>
    have hgate : weight S (DMFormula.and A B).eval ≤ weight S A.eval + weight S B.eval :=
      score_and _ _ _ _ _ _ _ _ _ _ _ _
    simp only [occ]
    omega
  | or A B ha hb =>
    have hgate : weight S (DMFormula.or A B).eval ≤ weight S A.eval + weight S B.eval :=
      score_or _ _ _ _ _ _ _ _ _ _ _ _
    simp only [occ]
    omega

def samples (r a b c : ℕ) : Samples (Fin 12 → Bool) :=
  let p := addr r a b
  let q := addr (r + 1) b c
  let z := addr (r + 2) c a
  let low := fun i => (i == addr r (1 - a) b) || (i == addr (r + 1) b (1 - c)) ||
    (i == addr (r + 2) (1 - c) a) || (i == addr (r + 2) c (1 - a))
  ⟨fun i => (i == p) || (i == q) || (i == z),
   fun i => (i == q) || (i == z),
   fun i => (i == p) || (i == z),
   low, fun i => low i || (i == p), fun i => low i || (i == q)⟩

theorem samples_spec : ∀ (r : Fin 3) (a b c : Fin 2),
    weight (samples r a b c) walk = 3 ∧
    ∀ i : Fin 12, weight (samples r a b c) (fun x => x i) =
      (if i = addr r a b then 1 else 0) + (if i = addr (r.val + 1) b c then 1 else 0) := by
  decide +kernel

theorem pair_bound (F : DMFormula 12) (hF : F.eval = walk)
    (r : Fin 3) (a b c : Fin 2) :
    3 ≤ occ F (addr r a b) + occ F (addr (r.val + 1) b c) := by
  obtain ⟨hw, hi⟩ := samples_spec r a b c
  have h := weight_le (samples r a b c) (addr r a b) (addr (r.val + 1) b c)
    (fun i => (hi i).le) F
  rwa [hF, hw] at h

theorem triangle_bound (F : DMFormula 12) (hF : F.eval = walk) (s t u : Fin 2) :
    5 ≤ occ F (addr 0 s t) + occ F (addr 1 t u) + occ F (addr 2 u s) := by
  have hab := pair_bound F hF 0 s t u
  have hbc := pair_bound F hF 1 t u s
  have hca := pair_bound F hF 2 u s t
  change 3 ≤ occ F (addr 0 s t) + occ F (addr 1 t u) at hab
  change 3 ≤ occ F (addr 1 t u) + occ F (addr 2 u s) at hbc
  change 3 ≤ occ F (addr 2 u s) + occ F (addr 3 s t) at hca
  have wrap : ∀ i j : Fin 2, addr 3 i j = addr 0 i j := by decide
  rw [wrap] at hca
  omega

theorem lower (F : DMFormula 12) (hF : F.eval = walk) : 20 ≤ F.leaves := by
  have h : 40 ≤ ∑ s : Fin 2, ∑ t : Fin 2, ∑ u : Fin 2,
      (occ F (addr 0 s t) + occ F (addr 1 t u) + occ F (addr 2 u s)) := by
    calc
      40 = ∑ _s : Fin 2, ∑ _t : Fin 2, ∑ _u : Fin 2, (5 : ℕ) := by decide
      _ ≤ _ := Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
        Finset.sum_le_sum fun u _ => triangle_bound F hF s t u
  have count : (∑ s : Fin 2, ∑ t : Fin 2, ∑ u : Fin 2,
      (occ F (addr 0 s t) + occ F (addr 1 t u) + occ F (addr 2 u s))) = 2 * F.leaves := by
    rw [leaves_eq]
    simp only [Fin.sum_univ_two, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
      Nat.add_zero]
    ring!
  rw [count] at h
  omega

end PEqualNP.Outside.L_clb_130

open PEqualNP.Outside.L_clb_130

theorem PEqualNP.Outside.L_clb_130 : (¬ (let addr := fun (r a b : ℕ) => (Fin.ofNat 12 (4 * r + a + 2 * b))
let accepts := fun (x : Fin 12 → Bool) =>
    ∃ s t u : Fin 2, x (addr 0 s.val t.val) = true ∧
      x (addr 1 t.val u.val) = true ∧ x (addr 2 u.val s.val) = true
∃ F : PEqualNP.MetaComplexity.DMFormula 12, F.leaves ≤ 19 ∧
    ∀ x, F.eval x = true ↔ accepts x)) := by
  rintro ⟨F, hsize, hF⟩
  have heval : F.eval = walk := by
    funext x
    rw [Bool.eq_iff_iff, walk, decide_eq_true_iff]
    exact hF x
  have := lower F heval
  omega

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_274_aux

open PEqualNP.ProofComplexity
open scoped BigOperators Classical

-- The block charging argument adapts the proof at c7472f276cc168d8db6947317adae31d829977e4,
-- lean/PEqualNP/Outside/L_pcx_273.lean, to restrictions to embedded ports.
private abbrev BCl (R : Type) (a : ℕ) := Clause (Sum R (Fin a))

private noncomputable def retained {R : Type} {m n a : ℕ}
    (e : Fin m × Fin n → R) (C : BCl R a) : Finset (Literal (Sum R (Fin a))) := by
  classical
  exact C.filter (fun l => ∃ p, l = (Sum.inl (e p), true))

private noncomputable def positive {R : Type} {a : ℕ} (C : BCl R a) :
    Finset (Literal (Sum R (Fin a))) := by
  classical
  exact C.filter (fun l => l.2 = true ∧ ∃ r : R, l.1 = Sum.inl r)

private theorem mem_retained {R : Type} {m n a : ℕ}
    {e : Fin m × Fin n → R} {C : BCl R a} {l : Literal (Sum R (Fin a))} :
    l ∈ retained e C ↔ l ∈ C ∧ ∃ p, l = (Sum.inl (e p), true) := by
  classical
  exact Finset.mem_filter

private theorem mem_positive {R : Type} {a : ℕ}
    {C : BCl R a} {l : Literal (Sum R (Fin a))} :
    l ∈ positive C ↔ l ∈ C ∧ l.2 = true ∧ ∃ r : R, l.1 = Sum.inl r := by
  classical
  exact Finset.mem_filter

private noncomputable def seeds {R : Type} {m n a : ℕ}
    (e : Fin m × Fin n → R) (C : BCl R a) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => ∃ i : Fin n, (Sum.inl (e (j, i)), true) ∈ C)

private theorem mem_seeds {R : Type} {m n a : ℕ}
    {e : Fin m × Fin n → R} {C : BCl R a} {j : Fin m} :
    j ∈ seeds e C ↔ ∃ i : Fin n, (Sum.inl (e (j, i)), true) ∈ C := by
  classical
  simp [seeds]

private theorem retained_subset {R : Type} {m n a : ℕ}
    (e : Fin m × Fin n → R) (C : BCl R a) : retained e C ⊆ positive C := by
  classical
  intro l hl
  obtain ⟨hC, p, rfl⟩ := Finset.mem_filter.mp hl
  exact Finset.mem_filter.mpr ⟨hC, rfl, e p, rfl⟩

private theorem seeds_le {R : Type} {m n a : ℕ}
    (e : Fin m × Fin n ↪ R) (C : BCl R a) : (seeds e C).card ≤ (retained e C).card := by
  classical
  let f : (seeds e C) → Literal (Sum R (Fin a)) := fun j =>
    (Sum.inl (e (j, Classical.choose (mem_seeds.mp j.property))), true)
  have hf : Function.Injective f := by
    intro j k h
    apply Subtype.ext
    exact congrArg Prod.fst (e.injective (Sum.inl.inj (congrArg Prod.fst h)))
  let f' : (seeds e C) → (retained e C) := fun j =>
    ⟨f j, Finset.mem_filter.mpr ⟨Classical.choose_spec (mem_seeds.mp j.property), _, rfl⟩⟩
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f' (fun j k h => hf (congrArg Subtype.val h))

private noncomputable def bad {R : Type} {m n : ℕ}
    (e : Fin m × Fin n → R) (α : Fin m → Fin n) (r : R) : Bool := by
  classical
  exact decide (∃ p : Fin m × Fin n, e p = r ∧ p.2 ≠ α p.1)

private theorem bad_true {R : Type} {m n : ℕ}
    (e : Fin m × Fin n → R) (α : Fin m → Fin n) (r : R) :
    bad e α r = true ↔ ∃ p : Fin m × Fin n, e p = r ∧ p.2 ≠ α p.1 := by
  classical
  simp only [bad, decide_eq_true_eq]

private theorem bad_apply {R : Type} {m n : ℕ} (e : Fin m × Fin n ↪ R)
    (α : Fin m → Fin n) (p : Fin m × Fin n) :
    bad e α (e p) = true ↔ p.2 ≠ α p.1 := by
  classical
  simp only [bad, decide_eq_true_eq]
  exact ⟨fun ⟨q, hq, h⟩ => (e.injective hq) ▸ h, fun h => ⟨p, rfl, h⟩⟩

private def rawSat {R : Type} {a : ℕ} (x : R → Bool) (C : BCl R a) : Prop :=
  ∃ (r : R) (b : Bool), (Sum.inl r, b) ∈ C ∧ x r = b

private theorem bad_count {R : Type} {m n a : ℕ}
    (e : Fin m × Fin n ↪ R) (C : BCl R a) :
    (Finset.univ.filter (fun α : Fin m → Fin n => ¬ rawSat (bad e α) C)).card ≤
      n ^ (m - (seeds e C).card) := by
  classical
  let P := seeds e C
  let S := Finset.univ.filter (fun α : Fin m → Fin n => ¬ rawSat (bad e α) C)
  let f : (Fin m → Fin n) → (↥(Pᶜ) → Fin n) := fun α j => α j
  have hinj : Set.InjOn f (↑S : Set _) := by
    intro α hα β hβ heq
    funext j
    by_cases hj : j ∈ P
    · obtain ⟨i, hi⟩ := mem_seeds.mp hj
      have fixed : ∀ γ ∈ S, i = γ j := by
        intro γ hγ
        by_contra hne
        exact (Finset.mem_filter.mp hγ).2 ⟨e (j, i), true, hi, (bad_apply e γ (j, i)).2 hne⟩
      exact (fixed α hα).symm.trans (fixed β hβ)
    · exact congrFun heq ⟨j, Finset.mem_compl.mpr hj⟩
  have h := Finset.card_le_card_of_injOn f (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_fun, Fintype.card_coe, P] using h

private theorem power_linear {n k : ℕ} (hn : 2 ≤ n) : k + 1 ≤ n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h := Nat.mul_le_mul ih hn
    omega

private theorem affine_power {n b k : ℕ} (hn : 2 ≤ n) (hb : 0 < b) :
    n ^ b * k ≤ n ^ k + n ^ b * (b - 1) ∧
    n ^ b * ((b + 1) * k) ≤ k * n ^ k + n ^ b * (b * b) := by
  by_cases h : k < b
  · have h₁ : k ≤ b - 1 := by omega
    have h₂ : (b + 1) * k ≤ b * b := by
      calc
        (b + 1) * k ≤ (b + 1) * (b - 1) := Nat.mul_le_mul_left _ h₁
        _ ≤ b * b := by
          obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
          change (b + 1 + 1) * (b + 1 - 1) ≤ (b + 1) * (b + 1)
          rw [Nat.add_sub_cancel]
          nlinarith
    exact ⟨(Nat.mul_le_mul_left _ h₁).trans (Nat.le_add_left ..),
      (Nat.mul_le_mul_left _ h₂).trans (Nat.le_add_left ..)⟩
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
    rw [pow_add]
    have hu : u + 1 ≤ n ^ u := power_linear hn
    have h₁ : b + u ≤ n ^ u + (b - 1) := by omega
    have h₂ : (b + 1) * (b + u) ≤ (b + u) * n ^ u + b * b := by
      have hm := Nat.mul_le_mul_left (b + u) hu
      nlinarith
    constructor
    · simpa [Nat.mul_add] using Nat.mul_le_mul_left (n ^ b) h₁
    · simpa [Nat.mul_add, mul_left_comm] using Nat.mul_le_mul_left (n ^ b) h₂

private theorem sum_affine {S : Type} (A : Finset S) (g F : S → ℕ)
    {N t b u v c : ℕ} (hA : A.card ≤ t) (hs : ∑ x ∈ A, g x = t * b)
    (hb : u * b = v + c)
    (h : ∀ x ∈ A, N * (u * g x) ≤ F x + N * c) :
    t * (N * v) ≤ ∑ x ∈ A, F x := by
  have hsum := Finset.sum_le_sum h
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    ← Finset.mul_sum, hs] at hsum
  rw [show N * (u * (t * b)) = t * (N * (u * b)) by ring, hb, Nat.mul_add, Nat.mul_add] at hsum
  have hcard := Nat.mul_le_mul_right (N * c) hA
  omega

private theorem per_bad {R : Type} [DecidableEq R] {m n a t b : ℕ}
    (e : Fin m × Fin n ↪ R) (hn : 2 ≤ n) (hb : 0 < b) (hm : 0 < m)
    (ht : t = min m (2 ^ a)) (hmul : m = t * b)
    (G : Finset (BCl R a)) (α : Fin m → Fin n)
    (hno : ¬ ∃ z : Fin a → Bool, Satisfies (Sum.elim (bad e α) z) (↑G : Set _))
    (hyes : ∀ j : Fin m, ∃ z : Fin a → Bool,
      Satisfies (Sum.elim (Function.update (bad e α) (e (j, α j)) true) z) (↑G : Set _)) :
    let D := G.filter (fun C => ¬ rawSat (bad e α) C)
    t * n ^ b ≤ ∑ C ∈ D, n ^ (seeds e C).card ∧
    m * n ^ b ≤ ∑ C ∈ D, (retained e C).card * n ^ (seeds e C).card ∧
    ∃ C ∈ G, b ≤ (retained e C).card := by
  classical
  intro D
  have hfalse : ∀ z : Fin a → Bool, ∃ C ∈ G, ¬ ClauseSat (Sum.elim (bad e α) z) C := by
    intro z
    by_contra! h
    exact hno ⟨z, fun C hC => h C hC⟩
  choose C hCG hC using hfalse
  choose z hz using hyes
  let φ := fun j => C (z j)
  let A := Finset.univ.image φ
  let g : BCl R a → ℕ := fun H => (Finset.univ.filter (fun j : Fin m => φ j = H)).card
  have hφ : ∀ j, (Sum.inl (e (j, α j)), true) ∈ φ j := by
    intro j
    obtain ⟨⟨v, bv⟩, hmem, hsat⟩ := hz j (φ j) (hCG (z j))
    cases v with
    | inr h => exact False.elim (hC (z j) ⟨(Sum.inr h, bv), hmem, hsat⟩)
    | inl r =>
      by_cases hr : r = e (j, α j)
      · subst r
        have : true = bv := by simpa using hsat
        simpa [← this] using hmem
      · exact False.elim (hC (z j) ⟨(Sum.inl r, bv), hmem, by
          simpa [Function.update, hr] using hsat⟩)
  have hAD : A ⊆ D := by
    intro H hH
    rcases Finset.mem_image.mp hH with ⟨j, _, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨hCG _, ?_⟩
    rintro ⟨r, bv, hl, hv⟩
    exact hC (z j) ⟨(Sum.inl r, bv), hl, hv⟩
  have hk : ∀ H, g H ≤ (seeds e H).card := by
    intro H
    apply Finset.card_le_card
    intro j hj
    have heq := (Finset.mem_filter.mp hj).2
    exact mem_seeds.mpr ⟨α j, heq ▸ hφ j⟩
  have hcard : A.card ≤ t := by
    rw [ht, le_min_iff]
    constructor
    · simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := φ))
    · have hsub : A ⊆ Finset.univ.image C := by
        intro H hH
        rcases Finset.mem_image.mp hH with ⟨j, _, rfl⟩
        exact Finset.mem_image.mpr ⟨z j, Finset.mem_univ _, rfl⟩
      exact (Finset.card_le_card hsub).trans (by
        simpa [Fintype.card_fun] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin a → Bool))) (f := C)))
  have hgs : ∑ H ∈ A, g H = m := by
    simp only [g, Finset.card_filter, Finset.sum_comm (s := A)]
    have hi : ∀ j : Fin m, (∑ H ∈ A, if φ j = H then 1 else 0) = 1 := by
      intro j
      rw [Finset.sum_ite_eq]
      simp [A]
    simp [hi]
  refine ⟨?_, ?_, ?_⟩
  · have h := sum_affine A g (fun H => n ^ (g H)) hcard (hgs.trans hmul)
        (N := n ^ b) (u := 1) (v := 1) (c := b - 1) (by omega)
        (fun H _ => by simpa using (affine_power (k := g H) hn hb).1)
    simp only [mul_one] at h
    refine h.trans ((Finset.sum_le_sum (fun H _ => ?_)).trans (Finset.sum_le_sum_of_subset hAD))
    exact Nat.pow_le_pow_right (by omega) (hk H)
  · have h := sum_affine A g (fun H => g H * n ^ (g H)) hcard (hgs.trans hmul)
        (N := n ^ b) (u := b + 1) (v := b) (c := b * b) (by ring)
        (fun H _ => (affine_power (k := g H) hn hb).2)
    rw [show t * (n ^ b * b) = m * n ^ b by rw [hmul]; ring] at h
    refine h.trans ((Finset.sum_le_sum (fun H _ => ?_)).trans (Finset.sum_le_sum_of_subset hAD))
    exact Nat.mul_le_mul ((hk H).trans (seeds_le e H)) (Nat.pow_le_pow_right (by omega) (hk H))
  · have hex : ∃ H ∈ A, b ≤ g H := by
      by_contra! h
      have hsum : ∑ H ∈ A, g H ≤ A.card * (b - 1) := by
        simpa using (Finset.sum_le_sum fun H hH => Nat.le_sub_one_of_lt (h H hH))
      have htpos : 0 < t := by
        by_contra! ht0
        have : t = 0 := by omega
        simp [this, Nat.ne_of_gt hm] at hmul
      have hlt : t * (b - 1) < t * b := Nat.mul_lt_mul_of_pos_left (by omega) htpos
      exact (not_lt_of_ge ((hsum.trans (Nat.mul_le_mul_right _ hcard)))) (by rwa [hgs, hmul])
    obtain ⟨H, hH, hg⟩ := hex
    exact ⟨H, (Finset.mem_filter.mp (hAD hH)).1, hg.trans ((hk H).trans (seeds_le e H))⟩

private theorem frameLower {R : Type} [DecidableEq R] {m n a t b : ℕ}
    (e : Fin m × Fin n ↪ R) (hn : 2 ≤ n) (hb : 0 < b) (hm : 0 < m)
    (ht : t = min m (2 ^ a)) (hmul : m = t * b) (G : Finset (BCl R a))
    (hno : ∀ α : Fin m → Fin n, ¬ ∃ z : Fin a → Bool,
      Satisfies (Sum.elim (bad e α) z) (↑G : Set _))
    (hyes : ∀ (α : Fin m → Fin n) (j : Fin m), ∃ z : Fin a → Bool,
      Satisfies (Sum.elim (Function.update (bad e α) (e (j, α j)) true) z) (↑G : Set _)) :
    t * n ^ b ≤ G.card ∧ m * n ^ b ≤ ∑ C ∈ G, (retained e C).card ∧
    ∃ C ∈ G, b ≤ (retained e C).card := by
  classical
  have hs : ∀ (c : ℕ) (f : BCl R a → ℕ),
      (∀ α : Fin m → Fin n, c ≤ ∑ C ∈ G.filter (fun C => ¬ rawSat (bad e α) C),
        f C * n ^ (seeds e C).card) → c ≤ ∑ C ∈ G, f C := by
    intro c f hc
    have h₁ : n ^ m * c ≤ ∑ α : Fin m → Fin n,
        ∑ C ∈ G.filter (fun C => ¬ rawSat (bad e α) C), f C * n ^ (seeds e C).card := by
      simpa [Fintype.card_fun, Fintype.card_fin] using
        (Finset.sum_le_sum fun α (_ : α ∈ (Finset.univ : Finset (Fin m → Fin n))) => hc α)
    have hswap : (∑ α : Fin m → Fin n,
        ∑ C ∈ G.filter (fun C => ¬ rawSat (bad e α) C), f C * n ^ (seeds e C).card) =
        ∑ C ∈ G, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ rawSat (bad e α) C)).card *
          (f C * n ^ (seeds e C).card) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have h₂ : (∑ C ∈ G, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ rawSat (bad e α) C)).card *
          (f C * n ^ (seeds e C).card)) ≤ n ^ m * ∑ C ∈ G, f C := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro C _
      have hle : (seeds e C).card ≤ m := by
        simpa using (Finset.card_le_card (Finset.subset_univ (seeds e C)))
      calc
        _ ≤ n ^ (m - (seeds e C).card) * (f C * n ^ (seeds e C).card) :=
          Nat.mul_le_mul_right _ (bad_count e C)
        _ = (n ^ (m - (seeds e C).card) * n ^ (seeds e C).card) * f C := by ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hswap] at h₁
    exact Nat.le_of_mul_le_mul_left (h₁.trans h₂) (pow_pos (by omega) _)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hs (t * n ^ b) (fun _ => 1) (fun α => by
      simpa using (per_bad e hn hb hm ht hmul G α (hno α) (hyes α)).1)
  · exact hs (m * n ^ b) (fun C => (retained e C).card) (fun α =>
      (per_bad e hn hb hm ht hmul G α (hno α) (hyes α)).2.1)
  · let α : Fin m → Fin n := fun _ => ⟨0, by omega⟩
    exact (per_bad e hn hb hm ht hmul G α (hno α) (hyes α)).2.2


open PEqualNP.ProofComplexity
open scoped BigOperators

private abbrev Word (n : ℕ) := Fin n → Bool
private abbrev Port (n w : ℕ) := Fin n × Word (w + 1)

private def cyc {n : ℕ} (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

private theorem cyc_comp {n : ℕ} (hn : 0 < n) (i : Fin n) (j k : ℕ) :
    cyc hn (cyc hn i j) k = cyc hn i (j + k) := by
  apply Fin.ext
  simp [cyc, Nat.mod_add_mod, Nat.add_assoc]

private theorem cyc_next {n : ℕ} (hn : 0 < n) (i : Fin n) (hi : i.val + 1 < n) :
    cyc hn i 1 = ⟨i.val + 1, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)

private theorem cyc_inj {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (i : Fin n) :
    Function.Injective (fun j : Fin k => cyc hn i j.val) := by
  intro u v h
  have h₁ : i.val + u.val ≡ i.val + v.val [MOD n] := congrArg Fin.val h
  have h₂ : u.val ≡ v.val [MOD n] := Nat.ModEq.add_left_cancel' i.val h₁
  apply Fin.ext
  have hu := Nat.mod_eq_of_lt (u.isLt.trans_le hk)
  have hv := Nat.mod_eq_of_lt (v.isLt.trans_le hk)
  simpa [Nat.ModEq, hu, hv] using h₂

private def window {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) (x : Word n) : Word k :=
  fun j => x (cyc hn i j.val)

private def wins {n w : ℕ} (hn : 0 < n) (T : Port n w → Bool) : Prop :=
  ∃ x : Word n, ∀ i : Fin n, T (i, window hn (w + 1) i x) = true

private theorem full_win_inj {n w : ℕ} (hn : 0 < n) (h : n ≤ w + 1) (i : Fin n) :
    Function.Injective (window hn (w + 1) i) := by
  have hs : Function.Surjective (fun j : Fin n => cyc hn i j.val) :=
    Finite.surjective_of_injective (cyc_inj hn le_rfl i)
  intro x y he
  funext q
  obtain ⟨j, rfl⟩ := hs q
  exact congrFun he (Fin.castLE h j)

private theorem word_family_short {n w m : ℕ} (hn : 0 < n) (L : Fin m → Word n)
    (hL : ∀ i : Fin n, Function.Injective (fun s => window hn w i (L s))) :
    ∀ x : Word n, (∀ i : Fin n, ∃ s : Fin m, window hn (w + 1) i (L s) = window hn (w + 1) i x) →
      ∃ s : Fin m, ∀ i : Fin n, window hn (w + 1) i (L s) = window hn (w + 1) i x := by
  intro x h
  choose s hs using h
  have hstep : ∀ i : Fin n, s i = s (cyc hn i 1) := by
    intro i
    apply hL (cyc hn i 1)
    funext j
    have h₁ := congrFun (hs i) ⟨j.val + 1, by omega⟩
    have h₂ := congrFun (hs (cyc hn i 1)) ⟨j.val, by omega⟩
    change L (s (cyc hn i 1)) (cyc hn (cyc hn i 1) j.val) =
      x (cyc hn (cyc hn i 1) j.val) at h₂
    change L (s i) (cyc hn i (j.val + 1)) = x (cyc hn i (j.val + 1)) at h₁
    rw [cyc_comp, Nat.add_comm 1 j.val] at h₂
    simpa [window, cyc_comp, Nat.add_comm 1 j.val] using h₁.trans h₂.symm
  let zero : Fin n := ⟨0, hn⟩
  have hui : ∀ k (hk : k < n), s zero = s ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hi : k < n := by omega
      have he := hstep ⟨k, hi⟩
      rw [cyc_next hn ⟨k, hi⟩ hk] at he
      exact (ih hi).trans he
  refine ⟨s zero, fun i => ?_⟩
  rw [hui i.val i.isLt]
  exact hs i

private theorem word_family_full {n w m : ℕ} (hn : 0 < n) (h : n ≤ w + 1)
    (L : Fin m → Word n) :
    ∀ x : Word n, (∀ i : Fin n, ∃ s : Fin m, window hn (w + 1) i (L s) = window hn (w + 1) i x) →
      ∃ s : Fin m, ∀ i : Fin n, window hn (w + 1) i (L s) = window hn (w + 1) i x := by
  intro x hx
  obtain ⟨s, h₀⟩ := hx ⟨0, hn⟩
  have he := full_win_inj hn h ⟨0, hn⟩ h₀
  exact ⟨s, fun i => congrArg (window hn (w + 1) i) he⟩

private def wordXor {n : ℕ} (x y : Word n) : Word n := fun i => xor (x i) (y i)

private theorem xor_right_inj (x : Bool) : Function.Injective (fun y => xor x y) := by
  intro u v h
  cases x <;> cases u <;> cases v <;> simp_all

private theorem xor_left_inj (x : Bool) : Function.Injective (fun y => xor y x) := by
  intro u v h
  cases x <;> cases u <;> cases v <;> simp_all

private theorem translated_proj {n k m : ℕ} (hn : 0 < n) (L : Fin m → Word n)
    (hL : ∀ i : Fin n, Function.Injective (fun s => window hn k i (L s))) (y : Word n) :
    ∀ i : Fin n, Function.Injective (fun s => window hn k i (wordXor (L s) y)) := by
  intro i s t h
  apply hL i
  funext j
  exact xor_left_inj (y (cyc hn i j.val)) (congrFun h j)

private theorem extend_proj {n k w m : ℕ} (hn : 0 < n) (hkw : k ≤ w + 1)
    (L : Fin m → Word n)
    (hL : ∀ i : Fin n, Function.Injective (fun s => window hn k i (L s))) :
    ∀ i : Fin n, Function.Injective (fun s => window hn (w + 1) i (L s)) := by
  intro i s t h
  apply hL i
  funext j
  exact congrFun h (Fin.castLE hkw j)

private def portEmbedding {n w m : ℕ} (hn : 0 < n) (L : Fin m → Word n)
    (hL : ∀ i : Fin n, Function.Injective (fun s => window hn (w + 1) i (L s))) :
    Fin m × Fin n ↪ Port n w where
  toFun p := (p.2, window hn (w + 1) p.2 (L p.1))
  inj' := by
    rintro ⟨s,i⟩ ⟨t,j⟩ h
    have he : i = j := congrArg Prod.fst h
    subst j
    exact Prod.ext (hL i (congrArg Prod.snd h)) rfl


private abbrev RegBit := ZMod 2

private def regIndex {n : ℕ} (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

private def regRestr {n w : ℕ} (hn : 0 < n)
    (S : Submodule RegBit (Fin n → RegBit)) (i : Fin n) : S →ₗ[RegBit] (Fin w → RegBit) :=
  (LinearMap.funLeft RegBit RegBit (fun j : Fin w => regIndex hn i j.val)).comp S.subtype

private def RegSpace (n w : ℕ) (hn : 0 < n) : Prop :=
  ∃ S : Submodule RegBit (Fin n → RegBit),
    ∀ i : Fin n, Function.Bijective (regRestr (w := w) hn S i)

private def regRotate {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n ≃ Fin n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact Equiv.addLeft i

private theorem regRotate_apply {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    regRotate hn i j = regIndex hn i j.val := rfl

private theorem regModSub {a b : ℕ} (h : b ≤ a) (h' : a - b < b) :
    a % b = a - b :=
  (Nat.mod_eq_sub_mod h).trans (Nat.mod_eq_of_lt h')

private def regCopyIndex {n w : ℕ} (hn : 0 < n) (i : Fin (n + w)) : Fin n :=
  ⟨i.val % n, Nat.mod_lt _ hn⟩

private theorem regCopyWindow {n w : ℕ} (hn : 0 < n) (hw : w ≤ n)
    (i : Fin (n + w)) :
    ∃ q : Fin n, ∃ p : Equiv.Perm (Fin w), ∀ j : Fin w,
      regCopyIndex hn (regIndex (by omega) i j.val) = regIndex hn q (p j).val := by
  have hi := i.isLt
  by_cases hi' : i.val < n
  · refine ⟨⟨i.val, hi'⟩, Equiv.refl _, ?_⟩
    intro j
    have hj := j.isLt
    apply Fin.ext
    change ((i.val + j.val) % (n + w)) % n = (i.val + j.val) % n
    rw [Nat.mod_eq_of_lt (show i.val + j.val < n + w by omega)]
  · have hwp : 0 < w := by omega
    refine ⟨⟨0, hn⟩, regRotate hwp ⟨i.val - n, by omega⟩, ?_⟩
    intro j
    have hj := j.isLt
    rw [regRotate_apply]
    apply Fin.ext
    change ((i.val + j.val) % (n + w)) % n = (0 + (i.val - n + j.val) % w) % n
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show (i.val - n + j.val) % w < n from
      (Nat.mod_lt _ hwp).trans_le hw)]
    by_cases h : i.val + j.val < n + w
    · rw [Nat.mod_eq_of_lt h, regModSub (show n ≤ i.val + j.val by omega)
        (show i.val + j.val - n < n by omega),
        Nat.mod_eq_of_lt (show i.val - n + j.val < w by omega)]
      omega
    · rw [regModSub (show n + w ≤ i.val + j.val by omega)
        (show i.val + j.val - (n + w) < n + w by omega),
        Nat.mod_eq_of_lt (show i.val + j.val - (n + w) < n by omega),
        regModSub (show w ≤ i.val - n + j.val by omega)
          (show i.val - n + j.val - w < w by omega)]
      omega

private theorem regReindexBijective {α β : Type*} (p : Equiv.Perm α) :
    Function.Bijective (fun f : α → β => f ∘ p) := by
  constructor
  · intro a b h
    funext j
    obtain ⟨k, rfl⟩ := p.surjective j
    exact congrFun h k
  · intro a
    exact ⟨a ∘ p.symm, funext fun j => congrArg a (p.symm_apply_apply j)⟩

private theorem regDuplicate {n w : ℕ} (hn : 0 < n) (hw : w ≤ n)
    (h : RegSpace n w hn) : RegSpace (n + w) w (by omega) := by
  obtain ⟨S, hS⟩ := h
  let c : S →ₗ[RegBit] (Fin (n + w) → RegBit) :=
    (LinearMap.funLeft RegBit RegBit (regCopyIndex (w := w) hn)).comp S.subtype
  have hc : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    funext j
    have hj := congrFun hxy ⟨j.val, by have := j.isLt; omega⟩
    change (x : Fin n → RegBit) ⟨j.val % n, _⟩ = (y : Fin n → RegBit) ⟨j.val % n, _⟩ at hj
    simpa only [Nat.mod_eq_of_lt j.isLt, Fin.eta] using hj
  let E := LinearEquiv.ofInjective c hc
  refine ⟨LinearMap.range c, fun i => ?_⟩
  obtain ⟨q, p, hp⟩ := regCopyWindow hn hw i
  have hf : (regRestr (w := w) (by omega) (LinearMap.range c) i : _ → _) =
      (fun f : Fin w → RegBit => f ∘ p) ∘ (regRestr hn S q) ∘ E.symm := by
    funext x j
    have hx : c (E.symm x) = (x : Fin (n + w) → RegBit) :=
      LinearEquiv.ofInjective_symm_apply c (h := hc) x
    change (x : Fin (n + w) → RegBit) (regIndex (by omega) i j.val) =
      (E.symm x : Fin n → RegBit) (regIndex hn q (p j).val)
    rw [← hx]
    change (E.symm x : Fin n → RegBit) (regCopyIndex hn (regIndex (by omega) i j.val)) = _
    rw [hp j]
  rw [hf]
  exact (regReindexBijective p).comp ((hS q).comp E.symm.bijective)

private theorem regPartition {n u w : ℕ} (hn : 0 < n) (huw : u + w = n)
    (i q : Fin n) :
    (∃ j : Fin u, regIndex hn i j.val = q) ∨
      (∃ j : Fin w, regIndex hn (regIndex hn i u) j.val = q) := by
  obtain ⟨j, rfl⟩ := (regRotate hn i).surjective q
  rw [regRotate_apply]
  have hj := j.isLt
  by_cases h : j.val < u
  · exact Or.inl ⟨⟨j.val, h⟩, rfl⟩
  · right
    refine ⟨⟨j.val - u, by omega⟩, Fin.ext ?_⟩
    change ((i.val + u) % n + (j.val - u)) % n = (i.val + j.val) % n
    rw [Nat.mod_add_mod, show i.val + u + (j.val - u) = i.val + j.val by omega]

private def regDot (n : ℕ) : LinearMap.BilinForm RegBit (Fin n → RegBit) :=
  dotProductBilin RegBit RegBit

private theorem regDotNondegenerate (n : ℕ) : (regDot n).Nondegenerate := by
  constructor
  · intro x h
    exact dotProduct_eq_zero x h
  · intro x h
    apply dotProduct_eq_zero x
    intro y
    exact (dotProduct_comm x y).trans (h y)

private theorem regComplement {n w u : ℕ} (hn : 0 < n) (hwu : w + u = n)
    (h : RegSpace n w hn) : RegSpace n u hn := by
  obtain ⟨S, hS⟩ := h
  have hdimS : Module.finrank RegBit S = w := by
    let E := LinearEquiv.ofBijective (regRestr (w := w) hn S ⟨0, hn⟩) (hS ⟨0, hn⟩)
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using E.finrank_eq
  let T := (regDot n).orthogonal S
  have hdim : Module.finrank RegBit T = Module.finrank RegBit (Fin u → RegBit) := by
    change Module.finrank RegBit ((regDot n).orthogonal S) = _
    rw [LinearMap.BilinForm.finrank_orthogonal (regDotNondegenerate n), hdimS]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  refine ⟨T, fun i => ?_⟩
  have hi : Function.Injective (regRestr (w := u) hn T i) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hx₀ (j : Fin u) : (x : Fin n → RegBit) (regIndex hn i j.val) = 0 :=
      congrFun hx j
    apply Subtype.ext
    funext q
    change (x : Fin n → RegBit) q = 0
    let δ : Fin n → RegBit := Pi.single q 1
    obtain ⟨y, hy⟩ := (hS (regIndex hn i u)).2
      (fun j : Fin w => δ (regIndex hn (regIndex hn i u) j.val))
    have hxy : dotProduct (y : Fin n → RegBit) (x : Fin n → RegBit) = 0 :=
      x.property (y : Fin n → RegBit) y.property
    have hdot : dotProduct δ (x : Fin n → RegBit) =
        dotProduct (y : Fin n → RegBit) (x : Fin n → RegBit) := by
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro r _
      rcases regPartition hn (by omega : u + w = n) i r with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hx₀ j, mul_zero, mul_zero]
      · have hy' : (y : Fin n → RegBit) (regIndex hn (regIndex hn i u) j.val) =
            δ (regIndex hn (regIndex hn i u) j.val) := congrFun hy j
        rw [hy']
    have hq : dotProduct (Pi.single q 1) (x : Fin n → RegBit) = 0 := hdot.trans hxy
    rwa [single_one_dotProduct] at hq
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

private theorem regZero (n : ℕ) (hn : 0 < n) : RegSpace n 0 hn := by
  refine ⟨⊥, fun _ => ⟨?_, ?_⟩⟩
  · intro x y _
    exact Subsingleton.elim x y
  · intro f
    exact ⟨0, funext fun j => Fin.elim0 j⟩

private theorem regSpaces (n : ℕ) :
    ∀ (hn : 0 < n) (w : ℕ), w ≤ n → RegSpace n w hn := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    have hsmall : ∀ w : ℕ, 2 * w ≤ n → RegSpace n w hn := by
      intro w hw
      by_cases hw0 : w = 0
      · subst w
        exact regZero n hn
      · have hpos : 0 < n - w := by omega
        have hlt : n - w < n := by omega
        have hle : w ≤ n - w := by omega
        have h := regDuplicate hpos hle (ih (n - w) hlt hpos w hle)
        have h' : ∀ hp : 0 < n - w + w, RegSpace (n - w + w) w hp :=
          fun _ => h
        rw [show n - w + w = n by omega] at h'
        exact h' hn
    intro w hw
    by_cases h : 2 * w ≤ n
    · exact hsmall w h
    · exact regComplement hn (w := n - w) (by omega) (hsmall (n - w) (by omega))

private theorem regBinaryWindows (n w : ℕ) (hn : 0 < n) (hw : w ≤ n) :
    ∃ l : (Fin w → Bool) ↪ (Fin n → Bool), ∀ i : Fin n,
      Function.Injective (fun s => fun j : Fin w =>
        l s ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) := by
  obtain ⟨S, hS⟩ := regSpaces n hn w hw
  let B : Bool ≃ RegBit := Fintype.equivOfCardEq (by
    change Fintype.card Bool = Fintype.card (ZMod 2)
    rw [Fintype.card_bool, ZMod.card])
  let E := LinearEquiv.ofBijective (regRestr (w := w) hn S ⟨0, hn⟩) (hS ⟨0, hn⟩)
  let enc : (Fin w → Bool) → S := fun s => E.symm (fun j => B (s j))
  have henc : Function.Injective enc := by
    intro a b hab
    have h := E.symm.injective hab
    funext j
    exact B.injective (congrFun h j)
  let f : (Fin w → Bool) → (Fin n → Bool) :=
    fun s j => B.symm ((enc s : Fin n → RegBit) j)
  have hwin (i : Fin n) : Function.Injective (fun s => fun j : Fin w =>
      f s (regIndex hn i j.val)) := by
    intro a b hab
    apply henc
    apply (hS i).1
    funext j
    exact B.symm.injective (congrFun hab j)
  have hf : Function.Injective f := by
    intro a b hab
    apply hwin ⟨0, hn⟩
    exact congrArg (fun (x : Fin n → Bool) (j : Fin w) => x (regIndex hn ⟨0, hn⟩ j.val)) hab
  exact ⟨⟨f, hf⟩, hwin⟩


open PEqualNP.ProofComplexity
open Classical

-- Partition and clause-family argument adapted from the pinned
-- c7472f276cc168d8db6947317adae31d829977e4:lean/PEqualNP/Outside/L_pcx_273.lean
-- (lines 55–510). Here blocks are Boolean words, with raw literals mapped
-- to row-tagged windows; every hidden group has the same size.

private abbrev FullHid (a : ℕ) := Clause (Fin a)

private lemma full_exists_partition_clauses (a : ℕ) :
    ∀ t : ℕ, 1 ≤ t → t ≤ 2 ^ a →
      ∃ U : Finset (FullHid a),
        U.card = t ∧
        (∀ z : Fin a → Bool, ∃! H : FullHid a, H ∈ U ∧ ¬ ClauseSat z H) ∧
        (∀ H ∈ U, ∃ z : Fin a → Bool, ¬ ClauseSat z H) := by
  intro t ht1
  induction t with
  | zero => omega
  | succ t ih =>
    intro htle
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨{∅}, Finset.card_singleton ∅, ?_, ?_⟩
      · intro z
        refine ⟨∅, ⟨Finset.mem_singleton_self ∅, ?_⟩, ?_⟩
        · rintro ⟨l, hl, _⟩; simp at hl
        · rintro H ⟨hH, _⟩; exact Finset.mem_singleton.mp hH
      · intro H hH
        rw [Finset.mem_singleton.mp hH]
        exact ⟨fun _ => false, by rintro ⟨l, hl, _⟩; simp at hl⟩
    · have ht1' : 1 ≤ t := by omega
      have htle' : t ≤ 2 ^ a := by omega
      obtain ⟨U, hUcard, hUuniq, hUex⟩ := ih ht1' htle'
      have hfree : ∃ H0 ∈ U, ∃ v0 : Fin a, (v0, true) ∉ H0 ∧ (v0, false) ∉ H0 := by
        by_contra hno
        push Not at hno
        have hfull : ∀ H ∈ U, ∀ v : Fin a, (v, true) ∈ H ∨ (v, false) ∈ H := by
          intro H hHU v
          by_cases ht : (v, true) ∈ H
          · exact Or.inl ht
          · exact Or.inr (hno H hHU v ht)
        let cls : (Fin a → Bool) → FullHid a := fun z => Classical.choose (hUuniq z)
        have hcls_mem : ∀ z : Fin a → Bool, cls z ∈ U :=
          fun z => (Classical.choose_spec (hUuniq z)).1.1
        have hcls_nsat : ∀ z : Fin a → Bool, ¬ ClauseSat z (cls z) :=
          fun z => (Classical.choose_spec (hUuniq z)).1.2
        have hinj : Set.InjOn cls (↑(Finset.univ : Finset (Fin a → Bool)) : Set _) := by
          intro z1 _ z2 _ hEq
          funext v
          rcases hfull (cls z1) (hcls_mem z1) v with hvt | hvf
          · have h1 : z1 v ≠ true := fun ht => hcls_nsat z1 ⟨(v, true), hvt, ht⟩
            have h2 : z2 v ≠ true := fun ht => hcls_nsat z2 ⟨(v, true), hEq ▸ hvt, ht⟩
            cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
          · have h1 : z1 v ≠ false := fun hf => hcls_nsat z1 ⟨(v, false), hvf, hf⟩
            have h2 : z2 v ≠ false := fun hf => hcls_nsat z2 ⟨(v, false), hEq ▸ hvf, hf⟩
            cases hz1 : z1 v <;> cases hz2 : z2 v <;> simp_all
        have hmaps : Set.MapsTo cls (↑(Finset.univ : Finset (Fin a → Bool)) : Set _) (↑U : Set _) :=
          fun z _ => Finset.mem_coe.mpr (hcls_mem z)
        have hle := Finset.card_le_card_of_injOn cls hmaps hinj
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hUcard] at hle
        omega
      obtain ⟨H0, hH0U, v0, hvt, hvf⟩ := hfree
      obtain ⟨z0, hz0⟩ := hUex H0 hH0U
      let H1 : FullHid a := insert (v0, true) H0
      let H2 : FullHid a := insert (v0, false) H0
      let z1 : Fin a → Bool := Function.update z0 v0 false
      let z2 : Fin a → Bool := Function.update z0 v0 true
      have hz1_H0 : ¬ ClauseSat z1 H0 := by
        rintro ⟨⟨v, b⟩, hmem, hsat⟩
        by_cases hv : v = v0
        · subst hv
          cases b
          · exact hvf hmem
          · exact hvt hmem
        · apply hz0
          refine ⟨(v, b), hmem, ?_⟩
          simpa [z1, Function.update, hv] using hsat
      have hz2_H0 : ¬ ClauseSat z2 H0 := by
        rintro ⟨⟨v, b⟩, hmem, hsat⟩
        by_cases hv : v = v0
        · subst hv
          cases b
          · exact hvf hmem
          · exact hvt hmem
        · apply hz0
          refine ⟨(v, b), hmem, ?_⟩
          simpa [z2, Function.update, hv] using hsat
      have hz1_H1 : ¬ ClauseSat z1 H1 := by
        rintro ⟨l, hl, hsat⟩
        rcases Finset.mem_insert.mp hl with rfl | hl0
        · simp [z1] at hsat
        · exact hz1_H0 ⟨l, hl0, hsat⟩
      have hz2_H2 : ¬ ClauseSat z2 H2 := by
        rintro ⟨l, hl, hsat⟩
        rcases Finset.mem_insert.mp hl with rfl | hl0
        · simp [z2] at hsat
        · exact hz2_H0 ⟨l, hl0, hsat⟩
      have hH1_ne_H2 : H1 ≠ H2 := by
        intro hEq
        have hmem : (v0, true) ∈ H2 := hEq ▸ Finset.mem_insert_self (v0, true) H0
        rcases Finset.mem_insert.mp hmem with h1 | h2
        · cases h1
        · exact hvt h2
      have hH1_not_er : H1 ∉ U.erase H0 := by
        intro hmem
        have h1 := (hUuniq z1).unique ⟨Finset.mem_of_mem_erase hmem, hz1_H1⟩ ⟨hH0U, hz1_H0⟩
        exact (Finset.mem_erase.mp hmem).1 h1
      have hH2_not_er : H2 ∉ U.erase H0 := by
        intro hmem
        have h1 := (hUuniq z2).unique ⟨Finset.mem_of_mem_erase hmem, hz2_H2⟩ ⟨hH0U, hz2_H0⟩
        exact (Finset.mem_erase.mp hmem).1 h1
      let U' : Finset (FullHid a) := insert H1 (insert H2 (U.erase H0))
      have hU'card : U'.card = t + 1 := by
        have hH1_not_ins : H1 ∉ insert H2 (U.erase H0) := by
          intro hmem
          rcases Finset.mem_insert.mp hmem with hEq | hEr
          · exact hH1_ne_H2 hEq
          · exact hH1_not_er hEr
        rw [Finset.card_insert_of_notMem hH1_not_ins, Finset.card_insert_of_notMem hH2_not_er,
          Finset.card_erase_of_mem hH0U, hUcard]
        omega
      refine ⟨U', hU'card, ?_, ?_⟩
      · intro z
        obtain ⟨Hz, ⟨hHzU, hHznsat⟩, hHzuniq⟩ := hUuniq z
        by_cases hEq : Hz = H0
        · subst Hz
          have her_sat : ∀ H ∈ U.erase H0, ClauseSat z H := by
            intro H hH
            by_contra hnsat
            exact (Finset.mem_erase.mp hH).1 (hHzuniq H ⟨Finset.mem_of_mem_erase hH, hnsat⟩)
          cases hzv : z v0
          · refine ⟨H1, ⟨Finset.mem_insert_self H1 _, ?_⟩, ?_⟩
            · rintro ⟨l, hl, hsat⟩
              rcases Finset.mem_insert.mp hl with rfl | hl0
              · rw [hzv] at hsat; cases hsat
              · exact hHznsat ⟨l, hl0, hsat⟩
            · rintro H ⟨hHU', hHnsat⟩
              rcases Finset.mem_insert.mp hHU' with rfl | hrest
              · rfl
              · rcases Finset.mem_insert.mp hrest with rfl | hEr
                · exfalso
                  exact hHnsat ⟨(v0, false), Finset.mem_insert_self _ _, hzv⟩
                · exact absurd (her_sat H hEr) hHnsat
          · refine ⟨H2, ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self H2 _), ?_⟩, ?_⟩
            · rintro ⟨l, hl, hsat⟩
              rcases Finset.mem_insert.mp hl with rfl | hl0
              · rw [hzv] at hsat; cases hsat
              · exact hHznsat ⟨l, hl0, hsat⟩
            · rintro H ⟨hHU', hHnsat⟩
              rcases Finset.mem_insert.mp hHU' with rfl | hrest
              · exfalso
                exact hHnsat ⟨(v0, true), Finset.mem_insert_self _ _, hzv⟩
              · rcases Finset.mem_insert.mp hrest with rfl | hEr
                · rfl
                · exact absurd (her_sat H hEr) hHnsat
        · have hH0sat : ClauseSat z H0 := by
            by_contra hnsat
            exact hEq (hHzuniq H0 ⟨hH0U, hnsat⟩).symm
          have hH1sat : ClauseSat z H1 := by
            obtain ⟨l, hl, hs⟩ := hH0sat
            exact ⟨l, Finset.mem_insert_of_mem hl, hs⟩
          have hH2sat : ClauseSat z H2 := by
            obtain ⟨l, hl, hs⟩ := hH0sat
            exact ⟨l, Finset.mem_insert_of_mem hl, hs⟩
          refine ⟨Hz, ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hEq, hHzU⟩)), hHznsat⟩, ?_⟩
          rintro H ⟨hHU', hHnsat⟩
          rcases Finset.mem_insert.mp hHU' with rfl | hrest
          · exact absurd hH1sat hHnsat
          · rcases Finset.mem_insert.mp hrest with rfl | hEr
            · exact absurd hH2sat hHnsat
            · exact hHzuniq H ⟨Finset.mem_of_mem_erase hEr, hHnsat⟩
      · intro H hHU'
        rcases Finset.mem_insert.mp hHU' with rfl | hrest
        · exact ⟨z1, hz1_H1⟩
        · rcases Finset.mem_insert.mp hrest with rfl | hEr
          · exact ⟨z2, hz2_H2⟩
          · exact hUex H (Finset.mem_of_mem_erase hEr)

private lemma full_exists_cover_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (g : α → ℕ) :
    ∀ S : Finset β, ∑ a ∈ U, g a = S.card →
      ∃ B : α → Finset β,
        (∀ a ∈ U, B a ⊆ S) ∧
        (∀ a ∈ U, (B a).card = g a) ∧
        (∀ j ∈ S, ∃ a ∈ U, j ∈ B a) := by
  induction U using Finset.induction_on with
  | empty =>
    intro S hS
    simp only [Finset.sum_empty] at hS
    have hSe : S = ∅ := Finset.card_eq_zero.mp hS.symm
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha
    · intro j hj; rw [hSe] at hj; simp at hj
  | insert a s ha ih =>
    intro S hS
    rw [Finset.sum_insert ha] at hS
    have hle : g a ≤ S.card := by omega
    obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hle
    have hcard_un : (S \ A).card + A.card = S.card := by
      have hdisj : Disjoint (S \ A) A := Finset.sdiff_disjoint
      have hun : (S \ A) ∪ A = S := Finset.sdiff_union_of_subset hAS
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hun] at hc
      exact hc.symm
    have hrem : ∑ x ∈ s, g x = (S \ A).card := by omega
    obtain ⟨B', hB'sub, hB'card, hB'cov⟩ := ih (S \ A) hrem
    refine ⟨fun x => if x = a then A else B' x, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAS]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact Finset.Subset.trans (hB'sub x hxs) Finset.sdiff_subset
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAcard]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact hB'card x hxs
    · intro j hj
      by_cases hjA : j ∈ A
      · exact ⟨a, Finset.mem_insert_self a s, by simp [hjA]⟩
      · have hjs : j ∈ S \ A := Finset.mem_sdiff.mpr ⟨hj, hjA⟩
        obtain ⟨x, hxs, hjx⟩ := hB'cov j hjs
        have hne : x ≠ a := fun h => ha (h ▸ hxs)
        exact ⟨x, Finset.mem_insert_of_mem hxs, by simp [hne, hjx]⟩

abbrev FullWord (n : ℕ) := Fin n → Bool
abbrev FullRaw (n w : ℕ) := Fin n × (Fin (w + 1) → Bool)
private abbrev FullCl (n w a : ℕ) := Clause (Sum (FullRaw n w) (Fin a))

def fullWindow {n w : ℕ} (hn : 0 < n) (i : Fin n) (x : FullWord n) :
    Fin (w + 1) → Bool :=
  fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

def fullPort {n w : ℕ} (hn : 0 < n) (p : FullWord n × Fin n) : FullRaw n w :=
  (p.2, fullWindow hn p.2 p.1)

lemma fullWindow_injective {n w : ℕ} (hn : 0 < n) (hfull : n ≤ w + 1) (i : Fin n) :
    Function.Injective (fullWindow (w := w) hn i) := by
  have hsurj : Function.Surjective (fun j : Fin (w + 1) =>
      (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n)) := by
    intro k
    have hi := i.isLt
    have hk := k.isLt
    by_cases h : i.val ≤ k.val
    · refine ⟨⟨k.val - i.val, by omega⟩, Fin.ext ?_⟩
      change (i.val + (k.val - i.val)) % n = k.val
      rw [show i.val + (k.val - i.val) = k.val by omega, Nat.mod_eq_of_lt hk]
    · refine ⟨⟨n + k.val - i.val, by omega⟩, Fin.ext ?_⟩
      change (i.val + (n + k.val - i.val)) % n = k.val
      rw [show i.val + (n + k.val - i.val) = k.val + n by omega, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hk]
  intro x y h
  funext k
  obtain ⟨j, hj⟩ := hsurj k
  have hj' : (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := hj
  simpa only [fullWindow, hj'] using congrFun h j

lemma fullPort_injective {n w : ℕ} (hn : 0 < n) (hfull : n ≤ w + 1) :
    Function.Injective (fullPort (w := w) hn) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ he
  have hij : i = j := congrArg Prod.fst he
  subst j
  have hxy : x = y := fullWindow_injective hn hfull i (congrArg Prod.snd he)
  subst y
  rfl

private noncomputable def fullHidPart {n w a : ℕ} (C : FullCl n w a) : FullHid a :=
  Finset.univ.filter (fun l : Fin a × Bool => (Sum.inr l.1, l.2) ∈ C)

private lemma full_mem_hidPart {n w a : ℕ} {C : FullCl n w a} {l : Fin a × Bool} :
    l ∈ fullHidPart C ↔ (Sum.inr l.1, l.2) ∈ C := by
  simp [fullHidPart]

private noncomputable def fullPosCount {n w a : ℕ} (C : FullCl n w a) : ℕ :=
  (C.filter (fun l => l.2 = true ∧ ∃ e : FullRaw n w, l.1 = Sum.inl e)).card

private noncomputable def fullMkClause {n w a : ℕ} (hn : 0 < n)
    (H : FullHid a) (B : Finset (FullWord n)) (f : ↥B → Fin n) : FullCl n w a :=
  H.image (fun l => (Sum.inr l.1, l.2)) ∪
    (Finset.univ : Finset ↥B).image (fun j => (Sum.inl (fullPort hn (j.1, f j)), true))

private lemma full_hidPart_mkClause {n w a : ℕ} (hn : 0 < n)
    (H : FullHid a) (B : Finset (FullWord n)) (f : ↥B → Fin n) :
    fullHidPart (fullMkClause (w := w) hn H B f) = H := by
  ext l
  rw [full_mem_hidPart, fullMkClause, Finset.mem_union]
  constructor
  · rintro (h1 | h2)
    · rcases Finset.mem_image.mp h1 with ⟨l', hl', hEq⟩
      rcases l with ⟨v, b⟩
      rcases l' with ⟨v', b'⟩
      injection hEq with hv hb
      injection hv with hv'
      subst hv'; subst hb
      exact hl'
    · rcases Finset.mem_image.mp h2 with ⟨j, _, hEq⟩
      cases hEq
  · intro hl
    exact Or.inl (Finset.mem_image.mpr ⟨l, hl, rfl⟩)

private lemma full_posCount_mkClause {n w a : ℕ} (hn : 0 < n) (hfull : n ≤ w + 1)
    (H : FullHid a) (B : Finset (FullWord n)) (f : ↥B → Fin n) :
    fullPosCount (fullMkClause (w := w) hn H B f) = B.card := by
  have hfilt : (fullMkClause (w := w) hn H B f).filter
      (fun l => l.2 = true ∧ ∃ e : FullRaw n w, l.1 = Sum.inl e) =
      (Finset.univ : Finset ↥B).image
        (fun j => (Sum.inl (fullPort hn (j.1, f j)), true)) := by
    ext l
    simp only [Finset.mem_filter, fullMkClause, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1 | h2, _, e, he⟩
      · rcases h1 with ⟨lh, _, rfl⟩
        cases he
      · exact h2
    · rintro ⟨j, rfl⟩
      exact ⟨Or.inr ⟨j, rfl⟩, rfl, fullPort hn (j.1, f j), rfl⟩
  rw [fullPosCount, hfilt]
  have hinj : Function.Injective (fun j : ↥B =>
      ((Sum.inl (fullPort hn (j.1, f j)) : Sum (FullRaw n w) (Fin a)), true)) := by
    intro j1 j2 hEq
    injection hEq with hv _
    injection hv with hp
    exact Subtype.ext (congrArg Prod.fst (fullPort_injective hn hfull hp))
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]

private lemma full_mkClause_injective {n w a : ℕ} (hn : 0 < n) (hfull : n ≤ w + 1)
    (H : FullHid a) (B : Finset (FullWord n)) :
    Function.Injective (fullMkClause (w := w) hn H B) := by
  intro f1 f2 hEq
  funext j
  have hmem : ((Sum.inl (fullPort hn (j.1, f1 j)) : Sum (FullRaw n w) (Fin a)), true) ∈
      fullMkClause hn H B f2 := by
    rw [← hEq, fullMkClause]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  rw [fullMkClause] at hmem
  rcases Finset.mem_union.mp hmem with h1 | h2
  · rcases Finset.mem_image.mp h1 with ⟨_, _, hC⟩
    cases hC
  · rcases Finset.mem_image.mp h2 with ⟨j', _, hC⟩
    injection hC with hv _
    injection hv with hp
    have hp' := fullPort_injective hn hfull hp
    have hj : j' = j := Subtype.ext (congrArg Prod.fst hp')
    subst j'
    exact (congrArg Prod.snd hp').symm

private lemma full_upper_core {n w a : ℕ} (hn : 0 < n) (hfull : n ≤ w + 1) :
    ∃ F : Finset (FullCl n w a),
      (∀ T : FullRaw n w → Bool,
        (∃ x : FullWord n, ∀ i : Fin n, T (fullPort hn (x, i)) = true) ↔
          ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _)) ∧
      F.card = 2 ^ min n a * n ^ (2 ^ (n - a)) ∧
      (∑ C ∈ F, fullPosCount C) = 2 ^ n * n ^ (2 ^ (n - a)) ∧
      (∀ C ∈ F, fullPosCount C ≤ 2 ^ (n - a)) ∧
      ∀ C ∈ F, ∀ e : FullRaw n w, (Sum.inl e, false) ∉ C := by
  let t : ℕ := 2 ^ min n a
  let b : ℕ := 2 ^ (n - a)
  have hprod : t * b = 2 ^ n := by
    have he : min n a + (n - a) = n := by
      by_cases h : n ≤ a
      · rw [min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.add_zero]
      · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
        omega
    change 2 ^ min n a * 2 ^ (n - a) = 2 ^ n
    rw [← pow_add, he]
  obtain ⟨U, hUcard, hUuniq, hUex⟩ := full_exists_partition_clauses a t
    (Nat.pow_pos (by omega)) (Nat.pow_le_pow_right (by omega) (Nat.min_le_right n a))
  have hsum : (∑ _H ∈ U, b) = (Finset.univ : Finset (FullWord n)).card := by
    rw [Finset.sum_const, smul_eq_mul, hUcard, hprod,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  obtain ⟨B, _, hBcard, hBcov⟩ :=
    full_exists_cover_card U (fun _ => b) (Finset.univ : Finset (FullWord n)) hsum
  let fam : FullHid a → Finset (FullCl n w a) := fun H =>
    (Finset.univ : Finset (↥(B H) → Fin n)).image (fullMkClause hn H (B H))
  let F : Finset (FullCl n w a) := U.biUnion fam
  have hdisj : Set.PairwiseDisjoint (↑U : Set (FullHid a)) fam := by
    intro H1 _ H2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro C hC1 hC2
    rcases Finset.mem_image.mp hC1 with ⟨f1, _, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨f2, _, hEq⟩
    have hhid := congrArg fullHidPart hEq
    rw [full_hidPart_mkClause, full_hidPart_mkClause] at hhid
    exact hne hhid.symm
  have hcount : F.card = t * n ^ b := by
    rw [Finset.card_biUnion hdisj]
    have hfam_card : ∀ H ∈ U, (fam H).card = n ^ b := by
      intro H hHU
      rw [Finset.card_image_of_injective _ (full_mkClause_injective hn hfull H (B H)),
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hBcard H hHU]
    rw [Finset.sum_congr rfl hfam_card, Finset.sum_const, smul_eq_mul, hUcard]
  have hpos : ∀ C ∈ F, fullPosCount C = b := by
    intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨H, hHU, hCH⟩
    rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
    rw [full_posCount_mkClause hn hfull, hBcard H hHU]
  refine ⟨F, ?_, hcount, ?_, fun C hC => (hpos C hC).le, ?_⟩
  · intro T
    constructor
    · rintro ⟨j0, hj0⟩
      obtain ⟨H0, hH0U, hj0B⟩ := hBcov j0 (Finset.mem_univ j0)
      obtain ⟨z, hzH0⟩ := hUex H0 hH0U
      have hz_other : ∀ H ∈ U, H ≠ H0 → ClauseSat z H := by
        intro H hHU hne
        by_contra hnsat
        exact hne ((hUuniq z).unique ⟨hHU, hnsat⟩ ⟨hH0U, hzH0⟩)
      refine ⟨z, ?_⟩
      intro C hC
      rcases Finset.mem_biUnion.mp (Finset.mem_coe.mp hC) with ⟨H, hHU, hCH⟩
      rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
      by_cases hEq : H = H0
      · subst hEq
        refine ⟨(Sum.inl (fullPort hn (j0, f ⟨j0, hj0B⟩)), true), ?_, ?_⟩
        · rw [fullMkClause]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j0, hj0B⟩, Finset.mem_univ _, rfl⟩)
        · exact hj0 (f ⟨j0, hj0B⟩)
      · obtain ⟨l, hlH, hlz⟩ := hz_other H hHU hEq
        refine ⟨(Sum.inr l.1, l.2), ?_, ?_⟩
        · rw [fullMkClause]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨l, hlH, rfl⟩)
        · exact hlz
    · rintro ⟨z, hz⟩
      by_contra hno
      push Not at hno
      obtain ⟨H0, ⟨hH0U, hH0nsat⟩, _⟩ := hUuniq z
      have hpick : ∀ j : ↥(B H0), ∃ i : Fin n, T (fullPort hn (j.1, i)) = false := by
        intro j
        obtain ⟨i, hi⟩ := hno j.1
        cases hx : T (fullPort hn (j.1, i))
        · exact ⟨i, hx⟩
        · exact False.elim (hi hx)
      let f : ↥(B H0) → Fin n := fun j => Classical.choose (hpick j)
      have hf : ∀ j : ↥(B H0), T (fullPort hn (j.1, f j)) = false :=
        fun j => Classical.choose_spec (hpick j)
      have hmem : fullMkClause (w := w) hn H0 (B H0) f ∈ (↑F : Set _) := by
        rw [Finset.mem_coe]
        exact Finset.mem_biUnion.mpr ⟨H0, hH0U, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩
      obtain ⟨l, hlC, hlsat⟩ := hz (fullMkClause hn H0 (B H0) f) hmem
      rw [fullMkClause] at hlC
      rcases Finset.mem_union.mp hlC with hl1 | hl2
      · rcases Finset.mem_image.mp hl1 with ⟨lh, hlh, rfl⟩
        exact hH0nsat ⟨lh, hlh, hlsat⟩
      · rcases Finset.mem_image.mp hl2 with ⟨j, _, rfl⟩
        have hxtrue : T (fullPort hn (j.1, f j)) = true := hlsat
        rw [hf j] at hxtrue
        cases hxtrue
  · change (∑ C ∈ F, fullPosCount C) = 2 ^ n * n ^ b
    rw [Finset.sum_congr rfl hpos, Finset.sum_const, smul_eq_mul, hcount, ← hprod]
    ring
  · intro C hC e hmem
    rcases Finset.mem_biUnion.mp hC with ⟨H, _, hCH⟩
    rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
    rw [fullMkClause] at hmem
    rcases Finset.mem_union.mp hmem with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨_, _, hEq⟩
      cases hEq
    · rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
      cases hEq

lemma full_upper {n w a : ℕ} (hn : 0 < n) (hfull : n ≤ w + 1) :
    let Pat := Fin (w + 1) → Bool
    let Raw := Fin n × Pat
    let Cl := Clause (Sum Raw (Fin a))
    let accepts := fun T : Raw → Bool => ∃ x : Fin n → Bool, ∀ i : Fin n,
      T (i, fun j : Fin (w + 1) => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true
    let enc := fun F : Finset Cl => ∀ T : Raw → Bool,
      accepts T ↔ ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑F : Set _)
    let pos := fun C : Cl => (C.filter (fun l =>
      l.2 = true ∧ ∃ e : Raw, l.1 = Sum.inl e)).card
    let d := if n ≤ w + 1 then n else w
    let ports := 2 ^ min n (w + 1)
    let groups := 2 ^ min d a
    let block := 2 ^ (d - a)
    ∃ F : Finset Cl, enc F ∧ F.card = groups * n ^ block ∧
      (∑ D ∈ F, pos D) = ports * n ^ block ∧ (∀ D ∈ F, pos D ≤ block) ∧
      ∀ D ∈ F, ∀ e : Raw, (Sum.inl e, false) ∉ D := by
  simp only [ite_eq_left hfull, min_eq_left hfull]
  obtain ⟨F, henc, hcard, hsum, hwidth, hnone⟩ := full_upper_core (a := a) hn hfull
  exact ⟨F, henc, hcard, hsum, hwidth, hnone⟩


private theorem frame_semantics {n w m : ℕ} (hn : 0 < n) (L : Fin m → Word n)
    (hL : ∀ i : Fin n, Function.Injective (fun s => window hn (w + 1) i (L s)))
    (hfamily : ∀ x : Word n,
      (∀ i : Fin n, ∃ s : Fin m, window hn (w + 1) i (L s) = window hn (w + 1) i x) →
      ∃ s : Fin m, ∀ i : Fin n, window hn (w + 1) i (L s) = window hn (w + 1) i x)
    (α : Fin m → Fin n) :
    let e := portEmbedding hn L hL
    ¬ wins hn (bad e α) ∧
      ∀ s : Fin m, wins hn (Function.update (bad e α) (e (s, α s)) true) := by
  classical
  intro e
  constructor
  · rintro ⟨x, hx⟩
    have hrows : ∀ i : Fin n, ∃ s : Fin m, window hn (w + 1) i (L s) = window hn (w + 1) i x := by
      intro i
      obtain ⟨⟨s,j⟩, he, _⟩ := (bad_true e α _).mp (hx i)
      have hji : j = i := congrArg Prod.fst he
      subst j
      exact ⟨s, congrArg Prod.snd he⟩
    obtain ⟨s, hs⟩ := hfamily x hrows
    have ht := hx (α s)
    rw [← hs (α s)] at ht
    exact (bad_apply e α (s, α s)).mp ht rfl
  · intro s
    refine ⟨L s, fun i => ?_⟩
    change Function.update (bad e α) (e (s, α s)) true (e (s,i)) = true
    by_cases hi : i = α s
    · simp [hi]
    · have he : e (s,i) ≠ e (s,α s) := fun h => hi (congrArg Prod.snd (e.injective h))
      rw [Function.update_of_ne he]
      exact (bad_apply e α (s,i)).mpr hi

private theorem translated_hit {n w m k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (hkw : k ≤ w + 1)
    (L : Fin m → Word n) (i : Fin n) (q : Word (w + 1)) :
    (Finset.univ.filter (fun y : Word n =>
      ∃ s : Fin m, window hn (w + 1) i (wordXor (L s) y) = q)).card ≤ m * 2 ^ (n-k) := by
  classical
  let D := Finset.univ.filter (fun y : Word n =>
    ∃ s : Fin m, window hn (w + 1) i (wordXor (L s) y) = q)
  let ψ : Fin k → Fin n := fun j => cyc hn i j.val
  let P := Finset.univ.image ψ
  have hP : P.card = k := by
    rw [Finset.card_image_of_injective _ (cyc_inj hn hkn i)]
    simp
  let s : D → Fin m := fun y => Classical.choose (Finset.mem_filter.mp y.property).2
  have hseed : ∀ y : D, window hn (w + 1) i (wordXor (L (s y)) y) = q :=
    fun y => Classical.choose_spec (Finset.mem_filter.mp y.property).2
  let f : D → Fin m × (↥(Pᶜ) → Bool) := fun y => (s y, fun z => y.val z)
  have hf : Function.Injective f := by
    intro y z he
    have hs : s y = s z := congrArg Prod.fst he
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ P
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hj
      have h₁ := congrFun (hseed y) (Fin.castLE hkw r)
      have h₂ := congrFun (hseed z) (Fin.castLE hkw r)
      rw [← hs] at h₂
      exact xor_right_inj (L (s y) (ψ r)) (h₁.trans h₂.symm)
    · exact congrFun (congrArg Prod.snd he) ⟨j, Finset.mem_compl.mpr hj⟩
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Finset.card_compl, hP] using Fintype.card_le_of_injective f hf

private theorem sum_translated {n w m : ℕ} (hn : 0 < n) (L : Fin m → Word n)
    (hL : ∀ y : Word n, ∀ i : Fin n, Function.Injective
      (fun s => window hn (w + 1) i (wordXor (L s) y))) {a : ℕ}
    (G : Finset (BCl (Port n w) a)) :
    let k := min n (w + 1)
    let e := fun y : Word n => portEmbedding hn (fun s => wordXor (L s) y) (hL y)
    (∑ y : Word n, ∑ C ∈ G, (retained (e y) C).card) ≤
      (m * 2 ^ (n-k)) * (∑ C ∈ G, (positive C).card) := by
  classical
  intro k e
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _
  let hit := fun (l : Literal (Sum (Port n w) (Fin a))) (y : Word n) =>
    ∃ p, l = (Sum.inl (e y p), true)
  have hEq : ∀ y, retained (e y) C = (positive C).filter (fun l => hit l y) := by
    intro y
    ext l
    constructor
    · intro hl
      exact Finset.mem_filter.mpr ⟨retained_subset (e y) C hl, (mem_retained.mp hl).2⟩
    · intro hl
      obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hl
      exact mem_retained.mpr ⟨(mem_positive.mp h₁).1, h₂⟩
  have hSwap : (∑ y : Word n, (retained (e y) C).card) =
      ∑ l ∈ positive C, (Finset.univ.filter (hit l)).card := by
    simp_rw [hEq, Finset.card_filter]
    exact Finset.sum_comm
  rw [hSwap]
  rw [show (m * 2 ^ (n - k)) * (positive C).card = ∑ _l ∈ positive C, m * 2 ^ (n - k) by
    simp [mul_comm]]
  apply Finset.sum_le_sum
  rintro ⟨v,b⟩ hl
  obtain ⟨_, hb, ⟨i,q⟩, hv⟩ := mem_positive.mp hl
  change b = true at hb
  change v = Sum.inl (i,q) at hv
  subst b
  subst v
  have heq : Finset.univ.filter (hit (Sum.inl (i,q), true)) =
      Finset.univ.filter (fun y : Word n => ∃ s : Fin m, window hn (w + 1) i (wordXor (L s) y) = q) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hit]
    constructor
    · rintro ⟨⟨s,j⟩, he⟩
      have h := Sum.inl.inj (congrArg Prod.fst he)
      have hij : i = j := congrArg Prod.fst h
      subst j
      exact ⟨s, (congrArg Prod.snd h).symm⟩
    · rintro ⟨s, hs⟩
      exact ⟨(s,i), by change (Sum.inl (i,q), true) = (Sum.inl (i, window hn _ i (wordXor (L s) y)), true); rw [hs]⟩
  rw [heq]
  exact translated_hit hn (min_le_left _ _) (min_le_right _ _) L i q

private noncomputable def labels (d : ℕ) : Fin (2 ^ d) ≃ Word d :=
  (Fintype.equivFinOfCardEq (by simp)).symm

private theorem block_arithmetic (d a : ℕ) :
    2 ^ min d a = min (2 ^ d) (2 ^ a) ∧
    2 ^ d = 2 ^ min d a * 2 ^ (d-a) := by
  constructor
  · by_cases h : d ≤ a
    · rw [min_eq_left h, min_eq_left (Nat.pow_le_pow_right (by omega) h)]
    · have h' : a ≤ d := by omega
      rw [min_eq_right h', min_eq_right (Nat.pow_le_pow_right (by omega) h')]
  · rw [← pow_add]
    congr 1
    omega

private theorem orbitLower {n w d a : ℕ} (hn : 0 < n) (hn₂ : 2 ≤ n) (L : Fin (2 ^ d) → Word n)
    (hL : ∀ y : Word n, ∀ i : Fin n, Function.Injective
      (fun s => window hn (w + 1) i (wordXor (L s) y)))
    (hfamily : ∀ y x : Word n,
      (∀ i : Fin n, ∃ s : Fin (2 ^ d), window hn (w + 1) i (wordXor (L s) y) = window hn (w + 1) i x) →
      ∃ s : Fin (2 ^ d), ∀ i : Fin n, window hn (w + 1) i (wordXor (L s) y) = window hn (w + 1) i x)
    (G : Finset (BCl (Port n w) a))
    (henc : ∀ T : Port n w → Bool, wins hn T ↔ ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑G : Set _)) :
    let b := 2 ^ (d-a)
    2 ^ min d a * n ^ b ≤ G.card ∧
      2 ^ min n (w + 1) * n ^ b ≤ (∑ C ∈ G, (positive C).card) ∧
      ∃ C ∈ G, b ≤ (positive C).card := by
  classical
  intro b
  let m := 2 ^ d
  let t := 2 ^ min d a
  let k := min n (w + 1)
  let e (y : Word n) := portEmbedding hn (fun s => wordXor (L s) y) (hL y)
  have hf (y : Word n) := frameLower (b := b) (e y) hn₂ (by positivity) (by positivity)
    (block_arithmetic d a).1 (block_arithmetic d a).2 G
    (fun α hz => (frame_semantics hn _ (hL y) (hfamily y) α).1 ((henc _).mpr hz))
    (fun α s => (henc _).mp ((frame_semantics hn _ (hL y) (hfamily y) α).2 s))
  obtain ⟨hc, _, C, hC, hw⟩ := hf (fun _ => false)
  refine ⟨hc, ?_, C, hC, hw.trans (Finset.card_le_card (retained_subset _ _))⟩
  have hsum : 2 ^ n * (m * n ^ b) ≤ ∑ y : Word n, ∑ C ∈ G, (retained (e y) C).card := by
    simpa [Fintype.card_fun] using
      (Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset (Word n))) => (hf y).2.1)
  have hfin := hsum.trans (sum_translated hn L hL G)
  have hp : 2 ^ n = 2 ^ (n-k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (min_le_left _ _)]
  rw [hp, show (2 ^ (n-k) * 2 ^ k) * (m * n ^ b) = (m * 2 ^ (n-k)) * (2 ^ k * n ^ b) by ring] at hfin
  exact Nat.le_of_mul_le_mul_left hfin (by positivity)

private theorem proofLower {n w a : ℕ} (hn : 0 < n) (hn₂ : 2 ≤ n)
    (G : Finset (BCl (Port n w) a))
    (henc : ∀ T : Port n w → Bool, wins hn T ↔ ∃ z : Fin a → Bool, Satisfies (Sum.elim T z) (↑G : Set _))
    (hreg : w + 1 < n → ∃ l : Word w ↪ Word n,
      ∀ i : Fin n, Function.Injective (fun s => window hn w i (l s))) :
    let d := if n ≤ w + 1 then n else w
    let b := 2 ^ (d-a)
    2 ^ min d a * n ^ b ≤ G.card ∧
      2 ^ min n (w + 1) * n ^ b ≤ (∑ C ∈ G, (positive C).card) ∧
      ∃ C ∈ G, b ≤ (positive C).card := by
  by_cases h : n ≤ w + 1
  · simp only [ite_eq_left h]
    let L := labels n
    have hL : ∀ i : Fin n, Function.Injective (fun s => window hn (w + 1) i (L s)) :=
      fun i => (full_win_inj hn h i).comp L.injective
    exact orbitLower hn hn₂ L (translated_proj hn L hL)
      (fun y => word_family_full hn h (fun s => wordXor (L s) y)) G henc
  · simp only [ite_eq_right h]
    obtain ⟨l, hl⟩ := hreg (by omega)
    let L := fun s => l (labels w s)
    have hL : ∀ i : Fin n, Function.Injective (fun s => window hn w i (L s)) :=
      fun i => (hl i).comp (labels w).injective
    exact orbitLower hn hn₂ L
      (fun y => extend_proj hn (by omega) _ (translated_proj hn L hL y))
      (fun y => word_family_short hn _ (translated_proj hn L hL y)) G henc

end PEqualNP.Outside.L_pcx_274_aux

open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_274_aux
open Classical

theorem PEqualNP.Outside.L_pcx_274 :
∀ (n w a : ℕ) (hn : 0 < n), 2 ≤ n →
  let Pat := Fin (w+1) → Bool
  let Raw := Fin n × Pat
  let Cl := PEqualNP.ProofComplexity.Clause (Sum Raw (Fin a))
  let accepts := fun T : Raw → Bool => ∃ x : Fin n → Bool, ∀ i : Fin n,
    T (i, fun j : Fin (w+1) => x ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩) = true
  let enc := fun F : Finset Cl => ∀ T : Raw → Bool,
    accepts T ↔ ∃ z : Fin a → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim T z) (↑F : Set _)
  let pos := fun C : Cl => (C.filter (fun l =>
    l.2 = true ∧ ∃ e : Raw, l.1 = Sum.inl e)).card
  let d := if n ≤ w+1 then n else w
  let ports := 2^(min n (w+1))
  let groups := 2^(min d a)
  let block := 2^(d-a)
  (∀ G : Finset Cl, enc G →
    groups * n^block ≤ G.card ∧ ports * n^block ≤ (∑ C ∈ G, pos C) ∧
      ∃ C ∈ G, block ≤ pos C) ∧
  (n ≤ w+1 → ∃ F : Finset Cl, enc F ∧ F.card = groups * n^block ∧
    (∑ D ∈ F, pos D) = ports * n^block ∧ (∀ D ∈ F, pos D ≤ block) ∧
    ∀ D ∈ F, ∀ e : Raw, (Sum.inl e, false) ∉ D) := by
  intro n w a hn hn₂
  dsimp only
  constructor
  · intro G hG
    have h := proofLower hn hn₂ G hG (fun hshort => regBinaryWindows n w hn (by omega))
    have hpos (C : BCl (Port n w) a) :
        positive C = C.filter (fun l => l.2 = true ∧ ∃ e : Port n w, l.1 = Sum.inl e) := by
      ext l
      simp only [mem_positive, Finset.mem_filter]
    simpa only [hpos] using h
  · intro hfull
    exact full_upper (a := a) hn hfull

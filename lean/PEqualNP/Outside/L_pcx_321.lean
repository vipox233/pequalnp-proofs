import PEqualNP.Defs
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_pcx_321_aux

open scoped BigOperators

def Lmin (n : ℕ) : ℕ := (15 * n + 31) / 32

def Umax (n : ℕ) : ℕ := (17 * n) / 32

lemma central_iff (n D : ℕ) : 16 * Nat.dist (2 * D) n ≤ n ↔ Lmin n ≤ D ∧ D ≤ Umax n := by
  dsimp only [Lmin, Umax, Nat.dist]
  omega

lemma fooling_bound {X A : Type*} [Fintype A] (accept : X → X → Prop) (u : ℕ)
    (left right : Fin u → X → Prop)
    (hcov : ∀ x z, accept x z ↔ ∃ t : Fin u, left t x ∧ right t z)
    (fx fz : A → X)
    (hdiag : ∀ a, accept (fx a) (fz a))
    (hoff : ∀ a b, a ≠ b → ¬ accept (fx a) (fz b) ∨ ¬ accept (fx b) (fz a)) :
    Fintype.card A ≤ u := by
  have hchoose : ∀ a : A, ∃ t : Fin u, left t (fx a) ∧ right t (fz a) :=
    fun a => (hcov (fx a) (fz a)).mp (hdiag a)
  let f : A → Fin u := fun a => Classical.choose (hchoose a)
  have hf : ∀ a : A, left (f a) (fx a) ∧ right (f a) (fz a) :=
    fun a => Classical.choose_spec (hchoose a)
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have h1 : accept (fx a) (fz b) := (hcov _ _).mpr ⟨f a, (hf a).1, hab ▸ (hf b).2⟩
    have h2 : accept (fx b) (fz a) := (hcov _ _).mpr ⟨f b, (hf b).1, hab.symm ▸ (hf a).2⟩
    rcases hoff a b hne with hn1 | hn2
    · exact hn1 h1
    · exact hn2 h2
  have hle := Fintype.card_le_of_injective f hinj
  simpa [Fintype.card_fin] using hle

def InS {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (false, i) ∈ S ∧ (true, M j i) ∈ S)

def OutS {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (false, i) ∉ S ∧ (true, M j i) ∉ S)

def CrossSet {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))

lemma disj_in_out {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Disjoint (InS M S j) (OutS M S j) := by
  rw [Finset.disjoint_left]
  intro i hi ho
  simp only [InS, OutS, Finset.mem_filter, Finset.mem_univ, true_and] at hi ho
  exact ho.1 hi.1

lemma disj_in_cross {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Disjoint (InS M S j) (CrossSet M S j) := by
  rw [Finset.disjoint_left]
  intro i hi hc
  simp only [InS, CrossSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hc
  exact hc ⟨fun _ => hi.2, fun _ => hi.1⟩

lemma disj_out_cross {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Disjoint (OutS M S j) (CrossSet M S j) := by
  rw [Finset.disjoint_left]
  intro i ho hc
  simp only [OutS, CrossSet, Finset.mem_filter, Finset.mem_univ, true_and] at ho hc
  exact hc ⟨fun h => absurd h ho.1, fun h => absurd h ho.2⟩

lemma union_in_out_cross {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n))
    (j : Fin r) :
    InS M S j ∪ OutS M S j ∪ CrossSet M S j = Finset.univ := by
  ext i
  simp only [InS, OutS, CrossSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  by_cases h1 : (false, i) ∈ S <;> by_cases h2 : (true, M j i) ∈ S <;> simp [h1, h2]

lemma filter_split_in_out_cross {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Bool × Fin n)) (j : Fin r) (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ((InS M S j).filter P).card + ((OutS M S j).filter P).card + ((CrossSet M S j).filter P).card := by
  have hunion : Finset.univ.filter P =
      (InS M S j).filter P ∪ (OutS M S j).filter P ∪ (CrossSet M S j).filter P := by
    rw [← union_in_out_cross M S j, Finset.filter_union, Finset.filter_union]
  rw [hunion]
  have hd1 : Disjoint ((InS M S j).filter P) ((OutS M S j).filter P) :=
    Finset.disjoint_filter_filter (disj_in_out M S j)
  have hd2 : Disjoint ((InS M S j).filter P ∪ (OutS M S j).filter P) ((CrossSet M S j).filter P) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter_filter (disj_in_cross M S j),
      Finset.disjoint_filter_filter (disj_out_cross M S j)⟩
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]

lemma card_in_out_cross {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Bool × Fin n)) (j : Fin r) :
    (InS M S j).card + (OutS M S j).card + (CrossSet M S j).card = n := by
  have h := filter_split_in_out_cross M S j (fun _ => True)
  simpa using h.symm

lemma card_S_eq {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n))
    (S : Finset (Bool × Fin n)) (j : Fin r) :
    S.card = 2 * (InS M S j).card + (CrossSet M S j).card := by
  let Sfalse : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)
  let Strue : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (true, M j i) ∈ S)
  have hSsplit : S = S.filter (fun v : Bool × Fin n => v.1 = false) ∪
      S.filter (fun v : Bool × Fin n => v.1 = true) := by
    ext ⟨b, i⟩
    cases b <;> simp
  have hSdisj : Disjoint (S.filter (fun v : Bool × Fin n => v.1 = false))
      (S.filter (fun v : Bool × Fin n => v.1 = true)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    cases h2.2
  have hSf : S.filter (fun v : Bool × Fin n => v.1 = false) = Sfalse.image (fun i => (false, i)) := by
    ext ⟨b, i⟩
    cases b <;> simp [Sfalse]
  have hSt : S.filter (fun v : Bool × Fin n => v.1 = true) = Strue.image (fun i => (true, M j i)) := by
    ext ⟨b, i⟩
    cases b
    · simp [Strue]
    · simp only [Finset.mem_filter, Finset.mem_image, Strue, Finset.mem_univ, true_and, Prod.mk.injEq,
        and_true]
      constructor
      · intro h
        refine ⟨(M j).symm i, ?_, (M j).apply_symm_apply i⟩
        simpa using h
      · rintro ⟨k, hk, rfl⟩
        exact hk
  have hcardSf : (S.filter (fun v : Bool × Fin n => v.1 = false)).card = Sfalse.card := by
    rw [hSf, Finset.card_image_of_injective]
    intro a b hab
    exact (Prod.mk.inj hab).2
  have hcardSt : (S.filter (fun v : Bool × Fin n => v.1 = true)).card = Strue.card := by
    rw [hSt, Finset.card_image_of_injective]
    intro a b hab
    exact (M j).injective (Prod.mk.inj hab).2
  have hScard : S.card = Sfalse.card + Strue.card := by
    conv_lhs => rw [hSsplit]
    rw [Finset.card_union_of_disjoint hSdisj, hcardSf, hcardSt]
  rw [hScard]
  have hsum1 : Sfalse.card + Strue.card =
      ∑ i : Fin n, ((if (false, i) ∈ S then 1 else 0) + (if (true, M j i) ∈ S then 1 else 0)) := by
    rw [Finset.sum_add_distrib]
    dsimp only [Sfalse, Strue]
    rw [Finset.card_filter, Finset.card_filter]
  have hsum2 : 2 * (InS M S j).card + (CrossSet M S j).card =
      ∑ i : Fin n, ((if (false, i) ∈ S ∧ (true, M j i) ∈ S then 2 else 0) +
        (if ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S) then 1 else 0)) := by
    rw [Finset.sum_add_distrib]
    have hA : 2 * (InS M S j).card = ∑ i : Fin n, if (false, i) ∈ S ∧ (true, M j i) ∈ S then 2 else 0 := by
      rw [InS, Finset.card_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      split_ifs <;> omega
    rw [hA]
    dsimp only [CrossSet]
    rw [Finset.card_filter]
  rw [hsum1, hsum2]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h1 : (false, i) ∈ S <;> by_cases h2 : (true, M j i) ∈ S <;> simp [h1, h2]

abbrev Summary (n r m : ℕ) : Type := (Fin r → Fin (n + 1)) × (Fin r × Fin m → Bool)

lemma card_summary (n r m : ℕ) : Fintype.card (Summary n r m) = (n + 1) ^ r * 2 ^ (r * m) := by
  simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

lemma upper_bound_cover (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) :
    let crosses := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
      ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))).card
    let m := Finset.univ.sup crosses
    let accept := fun (x z : (Bool × Fin n) → Bool) =>
      let w := fun v : Bool × Fin n => if v ∈ S then x v else z v
      ∀ j : Fin r,
        let D := (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j i))).card
        16 * Nat.dist (2 * D) n ≤ n
    ∃ left right : Fin ((n + 1) ^ r * 2 ^ (r * m)) → ((Bool × Fin n) → Bool) → Prop,
      ∀ x z : (Bool × Fin n) → Bool, accept x z ↔
        ∃ t : Fin ((n + 1) ^ r * 2 ^ (r * m)), left t x ∧ right t z := by
  classical
  intro crosses m accept
  have hcross_eq : ∀ j : Fin r, (CrossSet M S j).card = crosses j := fun j => rfl
  have hcross_le_m : ∀ j : Fin r, (CrossSet M S j).card ≤ m := fun j => by
    rw [hcross_eq j]
    exact Finset.le_sup (Finset.mem_univ j)
  let encSum : Summary n r m ≃ Fin ((n + 1) ^ r * 2 ^ (r * m)) :=
    Fintype.equivFinOfCardEq (card_summary n r m)
  let eCross : ∀ j : Fin r, CrossSet M S j ≃ Fin (CrossSet M S j).card :=
    fun j => Fintype.equivFinOfCardEq (Fintype.card_coe (CrossSet M S j))
  let tau : ((Bool × Fin n) → Bool) → Summary n r m := fun x =>
    (fun j => ⟨((InS M S j).filter (fun i => x (false, i) ≠ x (true, M j i))).card,
        Nat.lt_succ_of_le (le_trans (Finset.card_le_univ _) (by simp))⟩,
     fun jk =>
        if hk : jk.2.val < (CrossSet M S jk.1).card then
          let i := ((eCross jk.1).symm ⟨jk.2.val, hk⟩).val
          if (false, i) ∈ S then x (false, i) else x (true, M jk.1 i)
        else false)
  let evalD : Summary n r m → ((Bool × Fin n) → Bool) → Fin r → ℕ := fun s z j =>
    (s.1 j).val +
    ((OutS M S j).filter (fun i => z (false, i) ≠ z (true, M j i))).card +
    ((Finset.univ : Finset (CrossSet M S j)).filter (fun ic =>
      let k : Fin m := ⟨(eCross j ic).val, lt_of_lt_of_le (eCross j ic).isLt (hcross_le_m j)⟩
      (if (false, ic.val) ∈ S then s.2 (j, k) else z (false, ic.val)) ≠
      (if (false, ic.val) ∈ S then z (true, M j ic.val) else s.2 (j, k)))).card
  have heval : ∀ (x z : (Bool × Fin n) → Bool) (j : Fin r),
      evalD (tau x) z j =
        (Finset.univ.filter (fun i : Fin n =>
          (if (false, i) ∈ S then x (false, i) else z (false, i)) ≠
          (if (true, M j i) ∈ S then x (true, M j i) else z (true, M j i)))).card := by
    intro x z j
    let w : (Bool × Fin n) → Bool := fun v => if v ∈ S then x v else z v
    change evalD (tau x) z j = (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j i))).card
    rw [filter_split_in_out_cross M S j (fun i => w (false, i) ≠ w (true, M j i))]
    dsimp only [evalD]
    have h1 : ((tau x).1 j).val = ((InS M S j).filter (fun i => w (false, i) ≠ w (true, M j i))).card := by
      dsimp only [tau]
      congr 1
      refine Finset.filter_congr ?_
      intro i hi
      simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [w, hi.1, hi.2]
    have h2 : ((OutS M S j).filter (fun i => z (false, i) ≠ z (true, M j i))).card =
        ((OutS M S j).filter (fun i => w (false, i) ≠ w (true, M j i))).card := by
      congr 1
      refine Finset.filter_congr ?_
      intro i hi
      simp only [OutS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [w, hi.1, hi.2]
    have h3 : ((Finset.univ : Finset (CrossSet M S j)).filter (fun ic =>
        let k : Fin m := ⟨(eCross j ic).val, lt_of_lt_of_le (eCross j ic).isLt (hcross_le_m j)⟩
        (if (false, ic.val) ∈ S then (tau x).2 (j, k) else z (false, ic.val)) ≠
        (if (false, ic.val) ∈ S then z (true, M j ic.val) else (tau x).2 (j, k)))).card =
        ((CrossSet M S j).filter (fun i => w (false, i) ≠ w (true, M j i))).card := by
      refine Finset.card_bij (fun ic _ => ic.val) ?_ ?_ ?_
      · intro ic hic
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hic ⊢
        refine ⟨ic.2, ?_⟩
        have hc := ic.2
        simp only [CrossSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        have hlt : (eCross j ic).val < (CrossSet M S j).card := (eCross j ic).isLt
        have hsymm : (eCross j).symm ⟨(eCross j ic).val, hlt⟩ = ic := by
          exact (eCross j).symm_apply_apply ic
        have htau : (tau x).2 (j, ⟨(eCross j ic).val, lt_of_lt_of_le hlt (hcross_le_m j)⟩) =
            if (false, ic.val) ∈ S then x (false, ic.val) else x (true, M j ic.val) := by
          dsimp only [tau]
          rw [dite_eq_left hlt, hsymm]
        rw [htau] at hic
        by_cases hfs : (false, ic.val) ∈ S
        · have hts : (true, M j ic.val) ∉ S := fun hts => hc ⟨fun _ => hts, fun _ => hfs⟩
          simpa [w, hfs, hts] using hic
        · have hts : (true, M j ic.val) ∈ S := by
            by_contra hnts
            exact hc ⟨fun h => absurd h hfs, fun h => absurd h hnts⟩
          simpa [w, hfs, hts] using hic
      · intro ic1 _ ic2 _ heq
        exact Subtype.ext heq
      · intro i hi
        simp only [Finset.mem_filter] at hi
        refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hc := hi.1
        simp only [CrossSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        have hlt : (eCross j ⟨i, hi.1⟩).val < (CrossSet M S j).card := (eCross j ⟨i, hi.1⟩).isLt
        have hsymm : (eCross j).symm ⟨(eCross j ⟨i, hi.1⟩).val, hlt⟩ = ⟨i, hi.1⟩ := by
          exact (eCross j).symm_apply_apply ⟨i, hi.1⟩
        have htau : (tau x).2 (j, ⟨(eCross j ⟨i, hi.1⟩).val, lt_of_lt_of_le hlt (hcross_le_m j)⟩) =
            if (false, i) ∈ S then x (false, i) else x (true, M j i) := by
          dsimp only [tau]
          rw [dite_eq_left hlt, hsymm]
        rw [htau]
        by_cases hfs : (false, i) ∈ S
        · have hts : (true, M j i) ∉ S := fun hts => hc ⟨fun _ => hts, fun _ => hfs⟩
          simpa [w, hfs, hts] using hi.2
        · have hts : (true, M j i) ∈ S := by
            by_contra hnts
            exact hc ⟨fun h => absurd h hfs, fun h => absurd h hnts⟩
          simpa [w, hfs, hts] using hi.2
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) h1 h2) h3
  refine ⟨fun t x => encSum (tau x) = t,
    fun t z => ∀ j : Fin r, 16 * Nat.dist (2 * evalD (encSum.symm t) z j) n ≤ n, ?_⟩
  intro x z
  constructor
  · intro hacc
    refine ⟨encSum (tau x), rfl, ?_⟩
    intro j
    rw [encSum.symm_apply_apply, heval x z j]
    exact hacc j
  · rintro ⟨t, rfl, hright⟩
    intro j
    have hj := hright j
    rw [encSum.symm_apply_apply, heval x z j] at hj
    exact hj

lemma sum_sign_eq {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ∑ i ∈ s, (if P i then (1 : ℤ) else -1) = 2 * ((s.filter P).card : ℤ) - (s.card : ℤ) := by
  have h1 : ∑ i ∈ s, (if P i then (1 : ℤ) else -1) =
      ∑ i ∈ s, ((if P i then (2 : ℤ) else 0) - 1) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h : P i <;> simp [h]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ i ∈ s, (if P i then (2 : ℤ) else 0) = 2 * ((s.filter P).card : ℤ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h2]

lemma exists_le_of_sum_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℤ) (C : ℤ)
    (h : ∑ a : α, f a ≤ C * (Fintype.card α : ℤ)) :
    ∃ a : α, f a ≤ C := by
  by_contra hcontra
  push Not at hcontra
  have hstep : ∀ a : α, C + 1 ≤ f a := fun a => Int.add_one_le_of_lt (hcontra a)
  have hsum : (Fintype.card α : ℤ) * (C + 1) ≤ ∑ a : α, f a := by
    calc (Fintype.card α : ℤ) * (C + 1)
        = ∑ _a : α, (C + 1) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ a : α, f a := Finset.sum_le_sum (fun a _ => hstep a)
  have hpos : (0 : ℤ) < (Fintype.card α : ℤ) := Int.natCast_pos.mpr Fintype.card_pos
  nlinarith

lemma bool_not_ne_iff (a b : Bool) : ((!a) ≠ b) ↔ ¬ (a ≠ b) := by
  cases a <;> cases b <;> decide

lemma exists_pinned_base (n r : ℕ) (h8192 : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hcoinc : ∀ j l : Fin r, j ≠ l →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (j0 : Fin r) (A : Finset (Fin n)) (hA : 128 * A.card ≤ n)
    (d_target : ℕ) (hd : d_target ≤ n - A.card) :
    let UA : Finset (Bool × Fin n) :=
      A.image (fun i => (false, i)) ∪ A.image (fun i => (true, M j0 i))
    ∃ w0 : (Bool × Fin n) → Bool,
      ((Finset.univ \ A).filter (fun i : Fin n => w0 (false, i) ≠ w0 (true, M j0 i))).card = d_target ∧
      ∀ (w : (Bool × Fin n) → Bool), (∀ v, v ∉ UA → w v = w0 v) →
        ∀ j : Fin r, j ≠ j0 →
          16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j i))).card) n ≤ n := by
  classical
  intro UA
  let B : Finset (Fin n) := Finset.univ \ A
  have hBA_disj : Disjoint B A := Finset.sdiff_disjoint
  have hBA_union : B ∪ A = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ A)
  have hBA_card : B.card + A.card = n := by
    have h := Finset.card_union_of_disjoint hBA_disj
    rw [hBA_union, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hdB : d_target ≤ B.card := by omega
  obtain ⟨P, hPB, hPcard⟩ := Finset.exists_subset_card_eq hdB
  let ws : (B → Bool) → (Bool × Fin n) → Bool := fun s v =>
    match v with
    | (false, i) => if hi : i ∈ B then s ⟨i, hi⟩ else false
    | (true, b) =>
        let i := (M j0).symm b
        if hi : i ∈ B then xor (s ⟨i, hi⟩) (decide (i ∈ P)) else false
  have hws_j0 : ∀ s : B → Bool,
      (B.filter (fun i : Fin n => ws s (false, i) ≠ ws s (true, M j0 i))).card = d_target := by
    intro s
    have hfeq : B.filter (fun i : Fin n => ws s (false, i) ≠ ws s (true, M j0 i)) = P := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hiB, hne⟩
        dsimp only [ws] at hne
        rw [dite_eq_left hiB, (M j0).symm_apply_apply, dite_eq_left hiB] at hne
        by_contra hiP
        simp [hiP] at hne
      · intro hiP
        have hiB : i ∈ B := hPB hiP
        refine ⟨hiB, ?_⟩
        dsimp only [ws]
        rw [dite_eq_left hiB, (M j0).symm_apply_apply, dite_eq_left hiB]
        simp [hiP]
    rw [hfeq, hPcard]
  let Gj : Fin r → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i : Fin n => i ∈ B ∧ (M j0).symm (M j i) ∈ B ∧ M j i ≠ M j0 i)
  let Badj : Fin r → Finset (Fin n) := fun j => Finset.univ \ Gj j
  have hBad_bound : ∀ j : Fin r, j ≠ j0 → 128 * (Badj j).card ≤ 3 * n := by
    intro j hj
    have hsub : Badj j ⊆
        A ∪ A.image (fun t => (M j).symm (M j0 t)) ∪
          Finset.univ.filter (fun i : Fin n => M j i = M j0 i) := by
      intro i hi
      simp only [Badj, Gj, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and,
        not_and] at hi
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hiB : i ∈ B
      · by_cases hiB2 : (M j0).symm (M j i) ∈ B
        · right
          have hne := hi hiB hiB2
          exact not_not.mp hne
        · left
          right
          refine ⟨(M j0).symm (M j i), ?_, ?_⟩
          · simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hiB2
            exact hiB2
          · rw [(M j0).apply_symm_apply, (M j).symm_apply_apply]
      · left
        left
        simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hiB
        exact hiB
    have h1 : (Badj j).card ≤
        (A ∪ A.image (fun t => (M j).symm (M j0 t)) ∪
          Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := Finset.card_le_card hsub
    have h2 : (A ∪ A.image (fun t => (M j).symm (M j0 t)) ∪
        Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card ≤
        A.card + (A.image (fun t => (M j).symm (M j0 t))).card +
        (Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := by
      calc _ ≤ (A ∪ A.image (fun t => (M j).symm (M j0 t))).card +
              (Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := Finset.card_union_le _ _
        _ ≤ A.card + (A.image (fun t => (M j).symm (M j0 t))).card +
              (Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := by
            have := Finset.card_union_le A (A.image (fun t => (M j).symm (M j0 t)))
            omega
    have h3 : (A.image (fun t => (M j).symm (M j0 t))).card ≤ A.card := Finset.card_image_le
    have h4 := hcoinc j j0 hj
    omega
  let eta : Fin r → Fin n → (B → Bool) → ℤ := fun j i s =>
    if ws s (false, i) ≠ ws s (true, M j i) then 1 else -1
  have hortho : ∀ j : Fin r, ∀ i1 ∈ Gj j, ∀ i2 ∈ Gj j,
      i2 ≠ i1 → i2 ≠ (M j0).symm (M j i1) →
      ∑ s : B → Bool, eta j i1 s * eta j i2 s = 0 := by
    intro j i1 hi1 i2 hi2 hne1 hne2
    simp only [Gj, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rcases hi1 with ⟨hi1B, hi1'B, _⟩
    rcases hi2 with ⟨hi2B, hi2'B, hi2ne⟩
    let b2 : B := ⟨i2, hi2B⟩
    let flip2 : (B → Bool) ≃ (B → Bool) :=
      { toFun := fun s => Function.update s b2 (!(s b2))
        invFun := fun s => Function.update s b2 (!(s b2))
        left_inv := fun s => by
          funext x
          by_cases hx : x = b2
          · subst hx; simp
          · simp [Function.update, hx]
        right_inv := fun s => by
          funext x
          by_cases hx : x = b2
          · subst hx; simp
          · simp [Function.update, hx] }
    have hi2'ne : (M j0).symm (M j i2) ≠ i2 := by
      intro heq
      apply hi2ne
      have h := congrArg (M j0) heq
      simpa using h
    have hterm : ∀ s : B → Bool, eta j i1 (flip2 s) * eta j i2 (flip2 s) = -(eta j i1 s * eta j i2 s) := by
      intro s
      have he1 : eta j i1 (flip2 s) = eta j i1 s := by
        have hf1 : ws (flip2 s) (false, i1) = ws s (false, i1) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi1B, dite_eq_left hi1B]
          have hnb : (⟨i1, hi1B⟩ : B) ≠ b2 := fun h => hne1 (congrArg Subtype.val h).symm
          simp [Function.update, hnb]
        have ht1 : ws (flip2 s) (true, M j i1) = ws s (true, M j i1) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi1'B, dite_eq_left hi1'B]
          have hnb : (⟨(M j0).symm (M j i1), hi1'B⟩ : B) ≠ b2 :=
            fun h => hne2 (congrArg Subtype.val h).symm
          simp [Function.update, hnb]
        dsimp only [eta]
        rw [hf1, ht1]
      have he2 : eta j i2 (flip2 s) = -(eta j i2 s) := by
        have hf2 : ws (flip2 s) (false, i2) = !(ws s (false, i2)) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi2B, dite_eq_left hi2B]
          simp [b2]
        have ht2 : ws (flip2 s) (true, M j i2) = ws s (true, M j i2) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi2'B, dite_eq_left hi2'B]
          have hnb : (⟨(M j0).symm (M j i2), hi2'B⟩ : B) ≠ b2 :=
            fun h => hi2'ne (congrArg Subtype.val h)
          simp [Function.update, hnb]
        dsimp only [eta]
        rw [hf2, ht2]
        cases ws s (false, i2) <;> cases ws s (true, M j i2) <;> rfl
      rw [he1, he2]
      ring
    have hsum_eq : ∑ s : B → Bool, eta j i1 s * eta j i2 s =
        ∑ s : B → Bool, eta j i1 (flip2 s) * eta j i2 (flip2 s) :=
      (Fintype.sum_equiv flip2 (fun s => eta j i1 (flip2 s) * eta j i2 (flip2 s))
        (fun s => eta j i1 s * eta j i2 s) (fun _ => rfl)).symm
    have hneg : ∑ s : B → Bool, eta j i1 s * eta j i2 s =
        -(∑ s : B → Bool, eta j i1 s * eta j i2 s) := by
      calc ∑ s : B → Bool, eta j i1 s * eta j i2 s
          = ∑ s : B → Bool, eta j i1 (flip2 s) * eta j i2 (flip2 s) := hsum_eq
        _ = ∑ s : B → Bool, -(eta j i1 s * eta j i2 s) := Finset.sum_congr rfl (fun s _ => hterm s)
        _ = -(∑ s : B → Bool, eta j i1 s * eta j i2 s) := by rw [Finset.sum_neg_distrib]
    omega
  have hj_bound : ∀ j : Fin r,
      ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2 ≤ (2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ) := by
    intro j
    have hexp : ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2 =
        ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s := by
      calc ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2
          = ∑ s : B → Bool, ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, eta j i1 s * eta j i2 s := by
            refine Finset.sum_congr rfl ?_
            intro s _
            rw [sq, Finset.sum_mul_sum]
        _ = ∑ i1 ∈ Gj j, ∑ s : B → Bool, ∑ i2 ∈ Gj j, eta j i1 s * eta j i2 s := Finset.sum_comm
        _ = ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s := by
            refine Finset.sum_congr rfl ?_
            intro i1 _
            exact Finset.sum_comm
    rw [hexp]
    have hinner : ∀ i1 ∈ Gj j,
        ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s ≤ 2 * (Fintype.card (B → Bool) : ℤ) := by
      intro i1 hi1
      let T : Finset (Fin n) := {i1, (M j0).symm (M j i1)}
      have hfilt : ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s =
          ∑ i2 ∈ (Gj j).filter (fun i2 => i2 ∈ T), ∑ s : B → Bool, eta j i1 s * eta j i2 s := by
        symm
        refine Finset.sum_filter_of_ne ?_
        intro i2 hi2 hne
        by_contra hnotT
        simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or] at hnotT
        exact hne (hortho j i1 hi1 i2 hi2 hnotT.1 hnotT.2)
      rw [hfilt]
      have hterm_le : ∀ i2 : Fin n,
          ∑ s : B → Bool, eta j i1 s * eta j i2 s ≤ (Fintype.card (B → Bool) : ℤ) := by
        intro i2
        calc ∑ s : B → Bool, eta j i1 s * eta j i2 s
            ≤ ∑ _s : B → Bool, (1 : ℤ) := by
              refine Finset.sum_le_sum ?_
              intro s _
              dsimp only [eta]
              split_ifs <;> omega
          _ = (Fintype.card (B → Bool) : ℤ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hTcard : ((Gj j).filter (fun i2 => i2 ∈ T)).card ≤ 2 := by
        have hsubT : (Gj j).filter (fun i2 => i2 ∈ T) ⊆ T := by
          intro x hx
          exact (Finset.mem_filter.mp hx).2
        calc ((Gj j).filter (fun i2 => i2 ∈ T)).card
            ≤ T.card := Finset.card_le_card hsubT
          _ ≤ 2 := by
              dsimp only [T]
              exact le_trans (Finset.card_insert_le _ _) (by simp)
      calc ∑ i2 ∈ (Gj j).filter (fun i2 => i2 ∈ T), ∑ s : B → Bool, eta j i1 s * eta j i2 s
          ≤ ∑ _i2 ∈ (Gj j).filter (fun i2 => i2 ∈ T), (Fintype.card (B → Bool) : ℤ) :=
            Finset.sum_le_sum (fun i2 _ => hterm_le i2)
        _ = (((Gj j).filter (fun i2 => i2 ∈ T)).card : ℤ) * (Fintype.card (B → Bool) : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (Fintype.card (B → Bool) : ℤ) := by
            have hTcardZ : (((Gj j).filter (fun i2 => i2 ∈ T)).card : ℤ) ≤ 2 := by exact_mod_cast hTcard
            have hnonneg : (0 : ℤ) ≤ (Fintype.card (B → Bool) : ℤ) := Int.natCast_nonneg _
            nlinarith
    have hGcard : ((Gj j).card : ℤ) ≤ (n : ℤ) := by
      have h : (Gj j).card ≤ n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (Gj j)
      exact_mod_cast h
    have hnonneg : (0 : ℤ) ≤ (Fintype.card (B → Bool) : ℤ) := Int.natCast_nonneg _
    calc ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s
        ≤ ∑ _i1 ∈ Gj j, (2 * (Fintype.card (B → Bool) : ℤ)) :=
          Finset.sum_le_sum (fun i1 hi1 => hinner i1 hi1)
      _ = ((Gj j).card : ℤ) * (2 * (Fintype.card (B → Bool) : ℤ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℤ) * (2 * (Fintype.card (B → Bool) : ℤ)) := by nlinarith
      _ = (2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ) := by ring
  have htotal : ∑ s : B → Bool, ∑ j ∈ Finset.univ.erase j0, (∑ i ∈ Gj j, eta j i s) ^ 2 ≤
      (2 * (r : ℤ) * (n : ℤ)) * (Fintype.card (B → Bool) : ℤ) := by
    rw [Finset.sum_comm]
    have herase : ((Finset.univ.erase j0).card : ℤ) ≤ (r : ℤ) := by
      have h : (Finset.univ.erase j0).card ≤ r := by
        calc (Finset.univ.erase j0).card ≤ (Finset.univ : Finset (Fin r)).card :=
              Finset.card_le_card (Finset.erase_subset _ _)
          _ = r := by simp
      exact_mod_cast h
    have hnonneg : (0 : ℤ) ≤ (2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ) := by positivity
    calc ∑ j ∈ Finset.univ.erase j0, ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2
        ≤ ∑ _j ∈ Finset.univ.erase j0, ((2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ)) :=
          Finset.sum_le_sum (fun j _ => hj_bound j)
      _ = ((Finset.univ.erase j0).card : ℤ) * ((2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (r : ℤ) * ((2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ)) := by nlinarith
      _ = (2 * (r : ℤ) * (n : ℤ)) * (Fintype.card (B → Bool) : ℤ) := by ring
  obtain ⟨s0, hs0⟩ := exists_le_of_sum_le
    (fun s : B → Bool => ∑ j ∈ Finset.univ.erase j0, (∑ i ∈ Gj j, eta j i s) ^ 2)
    (2 * (r : ℤ) * (n : ℤ)) htotal
  refine ⟨ws s0, hws_j0 s0, ?_⟩
  intro w hw j hj
  have hsq_le : (∑ i ∈ Gj j, eta j i s0) ^ 2 ≤ 2 * (r : ℤ) * (n : ℤ) := by
    have hmem : j ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    exact le_trans
      (Finset.single_le_sum (fun k _ => sq_nonneg (∑ i ∈ Gj k, eta k i s0)) hmem) hs0
  have h8192Z : 8192 * (r : ℤ) < (n : ℤ) := by exact_mod_cast h8192
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have h32X : -(n : ℤ) ≤ 32 * (∑ i ∈ Gj j, eta j i s0) ∧
      32 * (∑ i ∈ Gj j, eta j i s0) ≤ (n : ℤ) := by
    have hsq32 : (32 * (∑ i ∈ Gj j, eta j i s0)) ^ 2 ≤ (n : ℤ) ^ 2 := by nlinarith
    constructor <;> nlinarith
  have hwG : ∀ i ∈ Gj j, w (false, i) = ws s0 (false, i) ∧ w (true, M j i) = ws s0 (true, M j i) := by
    intro i hi
    simp only [Gj, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hnf : (false, i) ∉ UA := by
      intro hmem
      simp only [UA, Finset.mem_union, Finset.mem_image] at hmem
      rcases hmem with ⟨a, ha, heq⟩ | ⟨a, _, heq⟩
      · have : a = i := (Prod.mk.inj heq).2
        subst this
        exact (Finset.mem_sdiff.mp hi.1).2 ha
      · exact Bool.false_ne_true (Prod.mk.inj heq).1.symm
    have hnt : (true, M j i) ∉ UA := by
      intro hmem
      simp only [UA, Finset.mem_union, Finset.mem_image] at hmem
      rcases hmem with ⟨a, _, heq⟩ | ⟨a, ha, heq⟩
      · exact Bool.false_ne_true (Prod.mk.inj heq).1
      · have hMeq : M j0 a = M j i := (Prod.mk.inj heq).2
        have hsymm : (M j0).symm (M j i) = a := by
          rw [← hMeq, (M j0).symm_apply_apply]
        have hnotA := (Finset.mem_sdiff.mp hi.2.1).2
        rw [hsymm] at hnotA
        exact hnotA ha
    exact ⟨hw (false, i) hnf, hw (true, M j i) hnt⟩
  let P : Fin n → Prop := fun i => w (false, i) ≠ w (true, M j i)
  have hG_Bad_disj : Disjoint (Gj j) (Badj j) := Finset.disjoint_sdiff
  have hG_Bad_union : Gj j ∪ Badj j = Finset.univ := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ (Gj j))
  have hcard_GB : (Gj j).card + (Badj j).card = n := by
    have h := Finset.card_union_of_disjoint hG_Bad_disj
    rw [hG_Bad_union, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hDsplit : (Finset.univ.filter P).card = ((Gj j).filter P).card + ((Badj j).filter P).card := by
    conv_lhs => rw [← hG_Bad_union]
    rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hG_Bad_disj)]
  have hDG_eq : ((Gj j).filter P).card =
      ((Gj j).filter (fun i => ws s0 (false, i) ≠ ws s0 (true, M j i))).card := by
    congr 1
    refine Finset.filter_congr ?_
    intro i hi
    rcases hwG i hi with ⟨hf, ht⟩
    simp [P, hf, ht]
  have hsign : ∑ i ∈ Gj j, eta j i s0 = 2 * (((Gj j).filter P).card : ℤ) - ((Gj j).card : ℤ) := by
    rw [hDG_eq]
    exact sum_sign_eq (Gj j) (fun i => ws s0 (false, i) ≠ ws s0 (true, M j i))
  have hDBad_le : ((Badj j).filter P).card ≤ (Badj j).card := Finset.card_filter_le _ _
  have hBad3 : 128 * (Badj j).card ≤ 3 * n := hBad_bound j hj
  rw [hsign] at h32X
  change 16 * Nat.dist (2 * (Finset.univ.filter P).card) n ≤ n
  dsimp only [Nat.dist]
  omega

lemma card_filter_lt_fin (q a : ℕ) (ha : a ≤ q) :
    (Finset.univ.filter (fun k : Fin q => k.val < a)).card = a := by
  have hbij : (Finset.univ.filter (fun k : Fin q => k.val < a)).card =
      (Finset.univ : Finset (Fin a)).card := by
    refine Finset.card_bij (fun k hk => (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin a)) ?_ ?_ ?_
    · intro k _; exact Finset.mem_univ _
    · intro k1 _ k2 _ heq
      exact Fin.ext (congrArg (fun x : Fin a => x.val) heq)
    · intro m _
      refine ⟨⟨m.val, lt_of_lt_of_le m.isLt ha⟩, ?_, Fin.ext rfl⟩
      simp
  rw [hbij]
  simp

end PEqualNP.Outside.L_pcx_321_aux

theorem PEqualNP.Outside.L_pcx_321 : (∃ N : ℕ, ∀ (n r : ℕ), N ≤ n → 0 < r → 8192*r < n →
  ∀ M : Fin r → Equiv.Perm (Fin n),
    (∀ j l : Fin r, j ≠ l →
      128*(Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
    let V := Bool × Fin n
    let X := V → Bool
    ∀ S : Finset V,
      let crosses := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
        ¬ ((false,i) ∈ S ↔ (true,M j i) ∈ S))).card
      let m := Finset.univ.sup crosses
      let accept := fun (x z : X) =>
        let w := fun v : V => if v ∈ S then x v else z v
        ∀ j : Fin r,
          let D := (Finset.univ.filter (fun i : Fin n => w (false,i) ≠ w (true,M j i))).card
          16 * Nat.dist (2*D) n ≤ n
      let cover := fun u : ℕ => ∃ left right : Fin u → X → Prop,
        ∀ x z : X, accept x z ↔ ∃ t : Fin u, left t x ∧ right t z
      cover ((n+1)^r * 2^(r*m)) ∧
      ∀ u : ℕ, cover u →
        2^(min m (n/128)) ≤ u ∧
        (n ≤ 2*S.card → 2*S.card ≤ 3*n → n/512+1 ≤ u)) := by
  classical
  refine ⟨65536, ?_⟩
  intro n r hn hr h8192 M hcoinc V X S crosses m accept cover
  refine ⟨PEqualNP.Outside.L_pcx_321_aux.upper_bound_cover n r M S, ?_⟩
  intro u hcov
  rcases hcov with ⟨left, right, hcov_iff⟩
  have hpart2 : 2 ^ (min m (n / 128)) ≤ u := by
    let k : ℕ := min m (n / 128)
    have huniv_ne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    obtain ⟨j0, _, hj0_eq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin r)) huniv_ne crosses
    have hk_le_cross : k ≤ (PEqualNP.Outside.L_pcx_321_aux.CrossSet M S j0).card := by
      have : (PEqualNP.Outside.L_pcx_321_aux.CrossSet M S j0).card = m := hj0_eq.symm
      rw [this]
      exact Nat.min_le_left m (n / 128)
    obtain ⟨Across, hAcross_sub, hAcross_card⟩ := Finset.exists_subset_card_eq hk_le_cross
    have hA128 : 128 * Across.card ≤ n := by
      have hk_le : k ≤ n / 128 := Nat.min_le_right m (n / 128)
      omega
    let L : ℕ := PEqualNP.Outside.L_pcx_321_aux.Lmin n
    let U : ℕ := PEqualNP.Outside.L_pcx_321_aux.Umax n
    have hkL : k ≤ L := by
      have hk_le : k ≤ n / 128 := Nat.min_le_right m (n / 128)
      dsimp only [L, PEqualNP.Outside.L_pcx_321_aux.Lmin]
      omega
    have hLU : L ≤ U := by
      dsimp only [L, U, PEqualNP.Outside.L_pcx_321_aux.Lmin, PEqualNP.Outside.L_pcx_321_aux.Umax]
      omega
    have hd_le : L - k ≤ n - Across.card := by
      dsimp only [L, PEqualNP.Outside.L_pcx_321_aux.Lmin]
      omega
    obtain ⟨w0, hw0_j0, hw0_other⟩ :=
      PEqualNP.Outside.L_pcx_321_aux.exists_pinned_base n r h8192 M hcoinc j0 Across hA128 (L - k) hd_le
    let UA : Finset (Bool × Fin n) :=
      Across.image (fun i => (false, i)) ∪ Across.image (fun i => (true, M j0 i))
    let fx : (Across → Bool) → X := fun α v =>
      match v with
      | (false, i) => if hi : i ∈ Across then α ⟨i, hi⟩ else w0 (false, i)
      | (true, b) =>
          if hi : (M j0).symm b ∈ Across then α ⟨(M j0).symm b, hi⟩ else w0 (true, b)
    let fz : (Across → Bool) → X := fun β v =>
      match v with
      | (false, i) => if hi : i ∈ Across then !(β ⟨i, hi⟩) else w0 (false, i)
      | (true, b) =>
          if hi : (M j0).symm b ∈ Across then !(β ⟨(M j0).symm b, hi⟩) else w0 (true, b)
    have hout : ∀ (α β : Across → Bool) (v : V), v ∉ UA →
        (if v ∈ S then fx α v else fz β v) = w0 v := by
      intro α β v hv
      rcases v with ⟨b, i⟩
      cases b
      · have hni : i ∉ Across := by
          intro hi
          apply hv
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        dsimp only [fx, fz]
        simp [hni]
      · have hni : (M j0).symm i ∉ Across := by
          intro hi
          apply hv
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(M j0).symm i, hi, by simp⟩)
        dsimp only [fx, fz]
        simp [hni]
    have hDj0 : ∀ (α β : Across → Bool),
        let w : X := fun v => if v ∈ S then fx α v else fz β v
        (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
          (L - k) + (Across.filter (fun i : Fin n =>
            if hi : i ∈ Across then α ⟨i, hi⟩ = β ⟨i, hi⟩ else False)).card := by
      intro α β
      let w : X := fun v => if v ∈ S then fx α v else fz β v
      change (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card = _
      have hun : (Finset.univ \ Across) ∪ Across = Finset.univ :=
        Finset.sdiff_union_of_subset (Finset.subset_univ Across)
      have hdj : Disjoint (Finset.univ \ Across) Across := Finset.sdiff_disjoint
      conv_lhs => rw [← hun]
      rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdj)]
      have h1 : ((Finset.univ \ Across).filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
          L - k := by
        rw [← hw0_j0]
        congr 1
        refine Finset.filter_congr ?_
        intro i hi
        have hni : i ∉ Across := (Finset.mem_sdiff.mp hi).2
        have hnf : (false, i) ∉ UA := by
          intro hm
          simp only [UA, Finset.mem_union, Finset.mem_image] at hm
          rcases hm with ⟨a, ha, heq⟩ | ⟨a, _, heq⟩
          · exact hni ((Prod.mk.inj heq).2 ▸ ha)
          · exact Bool.false_ne_true (Prod.mk.inj heq).1.symm
        have hnt : (true, M j0 i) ∉ UA := by
          intro hm
          simp only [UA, Finset.mem_union, Finset.mem_image] at hm
          rcases hm with ⟨a, _, heq⟩ | ⟨a, ha, heq⟩
          · exact Bool.false_ne_true (Prod.mk.inj heq).1
          · exact hni ((M j0).injective (Prod.mk.inj heq).2 ▸ ha)
        simp only [w, hout α β (false, i) hnf, hout α β (true, M j0 i) hnt]
      have h2 : (Across.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
          (Across.filter (fun i : Fin n =>
            if hi : i ∈ Across then α ⟨i, hi⟩ = β ⟨i, hi⟩ else False)).card := by
        congr 1
        refine Finset.filter_congr ?_
        intro i hi
        rw [dite_eq_left hi]
        have hcross := hAcross_sub hi
        simp only [PEqualNP.Outside.L_pcx_321_aux.CrossSet, Finset.mem_filter, Finset.mem_univ,
          true_and] at hcross
        by_cases hfs : (false, i) ∈ S
        · have hts : (true, M j0 i) ∉ S := fun hts => hcross ⟨fun _ => hts, fun _ => hfs⟩
          dsimp only [w, fx, fz]
          rw [ite_eq_left hfs, ite_eq_right hts, dite_eq_left hi, (M j0).symm_apply_apply, dite_eq_left hi]
          cases α ⟨i, hi⟩ <;> cases β ⟨i, hi⟩ <;> decide
        · have hts : (true, M j0 i) ∈ S := by
            by_contra hnts
            exact hcross ⟨fun h => absurd h hfs, fun h => absurd h hnts⟩
          dsimp only [w, fx, fz]
          rw [ite_eq_right hfs, ite_eq_left hts, dite_eq_left hi, (M j0).symm_apply_apply, dite_eq_left hi]
          cases α ⟨i, hi⟩ <;> cases β ⟨i, hi⟩ <;> decide
      rw [h1, h2]
    have hdiag : ∀ α : Across → Bool, accept (fx α) (fz α) := by
      intro α j
      by_cases hj : j = j0
      · subst hj
        rw [hDj0 α α]
        have hall : (Across.filter (fun i : Fin n =>
            if hi : i ∈ Across then α ⟨i, hi⟩ = α ⟨i, hi⟩ else False)).card = k := by
          have : Across.filter (fun i : Fin n =>
              if hi : i ∈ Across then α ⟨i, hi⟩ = α ⟨i, hi⟩ else False) = Across := by
            ext i
            simp only [Finset.mem_filter, and_iff_left_iff_imp]
            intro hi
            simp [hi]
          rw [this, hAcross_card]
        rw [hall, PEqualNP.Outside.L_pcx_321_aux.central_iff]
        dsimp only [L, U] at hkL hLU ⊢
        omega
      · exact hw0_other (fun v => if v ∈ S then fx α v else fz α v) (hout α α) j hj
    have hoff : ∀ α β : Across → Bool, α ≠ β →
        ¬ accept (fx α) (fz β) ∨ ¬ accept (fx β) (fz α) := by
      intro α β hne
      left
      intro hacc
      have hj0 := hacc j0
      rw [hDj0 α β, PEqualNP.Outside.L_pcx_321_aux.central_iff] at hj0
      have hex : ∃ ic : Across, α ic ≠ β ic := by
        by_contra hall
        push Not at hall
        exact hne (funext hall)
      obtain ⟨ic, hic⟩ := hex
      have hss : Across.filter (fun i : Fin n =>
          if hi : i ∈ Across then α ⟨i, hi⟩ = β ⟨i, hi⟩ else False) ⊂ Across := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have hm : ic.val ∈ Across.filter (fun i : Fin n =>
            if hi : i ∈ Across then α ⟨i, hi⟩ = β ⟨i, hi⟩ else False) := by
          rw [heq]
          exact ic.2
        simp only [Finset.mem_filter] at hm
        rw [dite_eq_left ic.2] at hm
        exact hic hm.2
      have hlt : (Across.filter (fun i : Fin n =>
          if hi : i ∈ Across then α ⟨i, hi⟩ = β ⟨i, hi⟩ else False)).card < k := by
        rw [← hAcross_card]
        exact Finset.card_lt_card hss
      dsimp only [L] at hkL hj0
      omega
    have hbound := PEqualNP.Outside.L_pcx_321_aux.fooling_bound accept u left right hcov_iff fx fz hdiag hoff
    have hcard : Fintype.card (Across → Bool) = 2 ^ k := by
      simp [Fintype.card_bool, hAcross_card]
    rw [hcard] at hbound
    exact hbound
  refine ⟨hpart2, ?_⟩
  intro hSlo hShi
  let q : ℕ := n / 512
  by_cases hm : n / 256 ≤ m
  · have hmin : n / 256 ≤ min m (n / 128) := le_min hm (by omega)
    have h1 : q + 1 ≤ n / 256 := by dsimp only [q]; omega
    have h2 : n / 256 ≤ 2 ^ (n / 256) := Nat.le_of_lt Nat.lt_two_pow_self
    have h3 : 2 ^ (n / 256) ≤ 2 ^ (min m (n / 128)) := Nat.pow_le_pow_right (by omega) hmin
    exact le_trans h1 (le_trans h2 (le_trans h3 hpart2))
  · push Not at hm
    let j0 : Fin r := ⟨0, hr⟩
    have hcross_lt : (PEqualNP.Outside.L_pcx_321_aux.CrossSet M S j0).card < n / 256 := by
      have hle : (PEqualNP.Outside.L_pcx_321_aux.CrossSet M S j0).card ≤ m :=
        Finset.le_sup (f := crosses) (Finset.mem_univ j0)
      omega
    have hScard := PEqualNP.Outside.L_pcx_321_aux.card_S_eq M S j0
    have htot := PEqualNP.Outside.L_pcx_321_aux.card_in_out_cross M S j0
    have hq_in : q ≤ (PEqualNP.Outside.L_pcx_321_aux.InS M S j0).card := by
      dsimp only [q]
      omega
    have hq_out : q ≤ (PEqualNP.Outside.L_pcx_321_aux.OutS M S j0).card := by
      dsimp only [q]
      omega
    obtain ⟨Ain, hAin_sub, hAin_card⟩ := Finset.exists_subset_card_eq hq_in
    obtain ⟨Aout, hAout_sub, hAout_card⟩ := Finset.exists_subset_card_eq hq_out
    have hdisj_io : Disjoint Ain Aout :=
      Disjoint.mono hAin_sub hAout_sub (PEqualNP.Outside.L_pcx_321_aux.disj_in_out M S j0)
    let Ares : Finset (Fin n) := Ain ∪ Aout
    have hAres_card : Ares.card = 2 * q := by
      dsimp only [Ares]
      rw [Finset.card_union_of_disjoint hdisj_io, hAin_card, hAout_card]
      omega
    have hAres128 : 128 * Ares.card ≤ n := by
      dsimp only [q] at hAres_card
      omega
    let L : ℕ := PEqualNP.Outside.L_pcx_321_aux.Lmin n
    let U : ℕ := PEqualNP.Outside.L_pcx_321_aux.Umax n
    have hqU : q ≤ U := by
      dsimp only [q, U, PEqualNP.Outside.L_pcx_321_aux.Umax]
      omega
    have hLU : L ≤ U := by
      dsimp only [L, U, PEqualNP.Outside.L_pcx_321_aux.Lmin, PEqualNP.Outside.L_pcx_321_aux.Umax]
      omega
    have hd_le : U - q ≤ n - Ares.card := by
      dsimp only [q, U, PEqualNP.Outside.L_pcx_321_aux.Umax] at hAres_card ⊢
      omega
    obtain ⟨w0, hw0_j0, hw0_other⟩ :=
      PEqualNP.Outside.L_pcx_321_aux.exists_pinned_base n r h8192 M hcoinc j0 Ares hAres128 (U - q) hd_le
    let UA : Finset (Bool × Fin n) :=
      Ares.image (fun i => (false, i)) ∪ Ares.image (fun i => (true, M j0 i))
    let ein : Ain ≃ Fin q := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hAin_card])
    let eout : Aout ≃ Fin q := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hAout_card])
    let fx : Fin (q + 1) → X := fun a v =>
      match v with
      | (false, i) => if i ∈ Ain then false else w0 (false, i)
      | (true, b) =>
          if hi : (M j0).symm b ∈ Ain then
            decide ((ein ⟨(M j0).symm b, hi⟩).val < a.val)
          else w0 (true, b)
    let fz : Fin (q + 1) → X := fun b v =>
      match v with
      | (false, i) => if i ∈ Aout then false else w0 (false, i)
      | (true, c) =>
          if hi : (M j0).symm c ∈ Aout then
            decide ((eout ⟨(M j0).symm c, hi⟩).val < q - b.val)
          else w0 (true, c)
    have hout : ∀ (a b : Fin (q + 1)) (v : V), v ∉ UA →
        (if v ∈ S then fx a v else fz b v) = w0 v := by
      intro a b v hv
      rcases v with ⟨fl, i⟩
      cases fl
      · have hni : i ∉ Ares := by
          intro hi
          apply hv
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
        have hnin : i ∉ Ain := fun hi => hni (Finset.mem_union_left _ hi)
        have hnout : i ∉ Aout := fun hi => hni (Finset.mem_union_right _ hi)
        dsimp only [fx, fz]
        simp [hnin, hnout]
      · have hni : (M j0).symm i ∉ Ares := by
          intro hi
          apply hv
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(M j0).symm i, hi, by simp⟩)
        have hnin : (M j0).symm i ∉ Ain := fun hi => hni (Finset.mem_union_left _ hi)
        have hnout : (M j0).symm i ∉ Aout := fun hi => hni (Finset.mem_union_right _ hi)
        dsimp only [fx, fz]
        simp [hnin, hnout]
    have hDj0 : ∀ (a b : Fin (q + 1)),
        let w : X := fun v => if v ∈ S then fx a v else fz b v
        (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
          (U - q) + a.val + (q - b.val) := by
      intro a b
      let w : X := fun v => if v ∈ S then fx a v else fz b v
      change (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card = _
      have hun : (Finset.univ \ Ares) ∪ (Ain ∪ Aout) = Finset.univ :=
        Finset.sdiff_union_of_subset (Finset.subset_univ Ares)
      have hdj1 : Disjoint (Finset.univ \ Ares) (Ain ∪ Aout) := Finset.sdiff_disjoint
      conv_lhs => rw [← hun]
      rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdj1)]
      rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj_io)]
      have h1 : ((Finset.univ \ Ares).filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
          U - q := by
        rw [← hw0_j0]
        congr 1
        refine Finset.filter_congr ?_
        intro i hi
        have hni : i ∉ Ares := (Finset.mem_sdiff.mp hi).2
        have hnf : (false, i) ∉ UA := by
          intro hm
          simp only [UA, Finset.mem_union, Finset.mem_image] at hm
          rcases hm with ⟨x, hx, heq⟩ | ⟨x, _, heq⟩
          · exact hni ((Prod.mk.inj heq).2 ▸ hx)
          · exact Bool.false_ne_true (Prod.mk.inj heq).1.symm
        have hnt : (true, M j0 i) ∉ UA := by
          intro hm
          simp only [UA, Finset.mem_union, Finset.mem_image] at hm
          rcases hm with ⟨x, _, heq⟩ | ⟨x, hx, heq⟩
          · exact Bool.false_ne_true (Prod.mk.inj heq).1
          · exact hni ((M j0).injective (Prod.mk.inj heq).2 ▸ hx)
        simp only [w, hout a b (false, i) hnf, hout a b (true, M j0 i) hnt]
      have h2 : (Ain.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card = a.val := by
        have hbij : (Ain.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
            (Finset.univ.filter (fun k : Fin q => k.val < a.val)).card := by
          refine Finset.card_bij (fun i hi => ein ⟨i, (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_
          · intro i hi
            rcases Finset.mem_filter.mp hi with ⟨hiA, hne⟩
            have hIn := hAin_sub hiA
            simp only [PEqualNP.Outside.L_pcx_321_aux.InS, Finset.mem_filter, Finset.mem_univ,
              true_and] at hIn
            dsimp only [w, fx] at hne
            rw [ite_eq_left hIn.1, ite_eq_left hIn.2, ite_eq_left hiA, (M j0).symm_apply_apply, dite_eq_left hiA] at hne
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hge
            simp [hge] at hne
          · intro i1 hi1 i2 hi2 heq
            exact congrArg Subtype.val (ein.injective heq)
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            let ic := ein.symm k
            refine ⟨ic.val, ?_, by simp [ic]⟩
            rw [Finset.mem_filter]
            refine ⟨ic.2, ?_⟩
            have hIn := hAin_sub ic.2
            simp only [PEqualNP.Outside.L_pcx_321_aux.InS, Finset.mem_filter, Finset.mem_univ,
              true_and] at hIn
            dsimp only [w, fx]
            rw [ite_eq_left hIn.1, ite_eq_left hIn.2, ite_eq_left ic.2, (M j0).symm_apply_apply, dite_eq_left ic.2]
            have hek : ein ⟨ic.val, ic.2⟩ = k := ein.apply_symm_apply k
            rw [hek]
            simp [hk]
        rw [hbij, PEqualNP.Outside.L_pcx_321_aux.card_filter_lt_fin q a.val (Nat.le_of_lt_succ a.isLt)]
      have h3 : (Aout.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card = q - b.val := by
        have hbij : (Aout.filter (fun i : Fin n => w (false, i) ≠ w (true, M j0 i))).card =
            (Finset.univ.filter (fun k : Fin q => k.val < q - b.val)).card := by
          refine Finset.card_bij (fun i hi => eout ⟨i, (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_
          · intro i hi
            rcases Finset.mem_filter.mp hi with ⟨hiA, hne⟩
            have hOut := hAout_sub hiA
            simp only [PEqualNP.Outside.L_pcx_321_aux.OutS, Finset.mem_filter, Finset.mem_univ,
              true_and] at hOut
            dsimp only [w, fz] at hne
            rw [ite_eq_right hOut.1, ite_eq_right hOut.2, ite_eq_left hiA, (M j0).symm_apply_apply, dite_eq_left hiA] at hne
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_contra hge
            simp [hge] at hne
          · intro i1 hi1 i2 hi2 heq
            exact congrArg Subtype.val (eout.injective heq)
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
            let ic := eout.symm k
            refine ⟨ic.val, ?_, by simp [ic]⟩
            rw [Finset.mem_filter]
            refine ⟨ic.2, ?_⟩
            have hOut := hAout_sub ic.2
            simp only [PEqualNP.Outside.L_pcx_321_aux.OutS, Finset.mem_filter, Finset.mem_univ,
              true_and] at hOut
            dsimp only [w, fz]
            rw [ite_eq_right hOut.1, ite_eq_right hOut.2, ite_eq_left ic.2, (M j0).symm_apply_apply, dite_eq_left ic.2]
            have hek : eout ⟨ic.val, ic.2⟩ = k := eout.apply_symm_apply k
            rw [hek]
            simp [hk]
        rw [hbij, PEqualNP.Outside.L_pcx_321_aux.card_filter_lt_fin q (q - b.val) (Nat.sub_le q b.val)]
      rw [h1, h2, h3]
      omega
    have hdiag : ∀ a : Fin (q + 1), accept (fx a) (fz a) := by
      intro a j
      by_cases hj : j = j0
      · subst hj
        rw [hDj0 a a, PEqualNP.Outside.L_pcx_321_aux.central_iff]
        have ha : a.val ≤ q := Nat.le_of_lt_succ a.isLt
        dsimp only [L, U] at hqU hLU ⊢
        omega
      · exact hw0_other (fun v => if v ∈ S then fx a v else fz a v) (hout a a) j hj
    have hoff : ∀ a b : Fin (q + 1), a ≠ b →
        ¬ accept (fx a) (fz b) ∨ ¬ accept (fx b) (fz a) := by
      intro a b hne
      have hvne : a.val ≠ b.val := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hvne with hlt | hgt
      · right
        intro hacc
        have hj0 := hacc j0
        rw [hDj0 b a, PEqualNP.Outside.L_pcx_321_aux.central_iff] at hj0
        have ha : a.val ≤ q := Nat.le_of_lt_succ a.isLt
        have hb : b.val ≤ q := Nat.le_of_lt_succ b.isLt
        dsimp only [U] at hqU hj0
        omega
      · left
        intro hacc
        have hj0 := hacc j0
        rw [hDj0 a b, PEqualNP.Outside.L_pcx_321_aux.central_iff] at hj0
        have ha : a.val ≤ q := Nat.le_of_lt_succ a.isLt
        have hb : b.val ≤ q := Nat.le_of_lt_succ b.isLt
        dsimp only [U] at hqU hj0
        omega
    have hbound := PEqualNP.Outside.L_pcx_321_aux.fooling_bound accept u left right hcov_iff fx fz hdiag hoff
    simpa [Fintype.card_fin, q] using hbound

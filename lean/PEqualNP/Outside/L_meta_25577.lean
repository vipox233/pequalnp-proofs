import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25577_aux

private def admissible (d t n m : Nat) (G : Fin n → Fin m → Bool) (edge : Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) : Prop :=
  let nbrR := fun (row : Fin n) => Finset.univ.filter (fun dest : Fin m => G row dest = edge)
  let nbrC := fun (col : Fin m) => Finset.univ.filter (fun src : Fin n => G src col = edge)
  let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
  let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
  let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ rowPol)
  let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ colPol)
  (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) ∧
  (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) ∧
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) ∧
  rowTypes.card ≤ t ∧ colTypes.card ≤ t ∧
  ∃ mark : Bool, ∀ a ∈ coreRows mark, ∀ b ∈ coreRows mark,
    ∀ x ∈ coreCols mark, ∀ y ∈ coreCols mark,
      G a x = mark → G b x = mark → G b y = mark → G a y = mark

private theorem card_image_le_of_eq_imp {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (hfg : ∀ a ∈ s, ∀ b ∈ s, f a = f b → g a = g b) :
    (s.image g).card ≤ (s.image f).card := by
  classical
  by_cases hne : s.Nonempty
  · rcases hne with ⟨a0, _⟩
    have hsurj : ∀ y : γ, ∃ x : β, y ∈ s.image g →
        x ∈ s.image f ∧ ∃ a ∈ s, g a = y ∧ f a = x := by
      intro y
      by_cases hy : y ∈ s.image g
      · rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
        exact ⟨f a, fun _ => ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, a, ha, rfl, rfl⟩⟩
      · exact ⟨f a0, fun h1 => absurd h1 hy⟩
    choose φ hφ using hsurj
    refine Finset.card_le_card_of_injOn φ (fun y hy => (hφ y hy).1) ?_
    intro y₁ hy₁ y₂ hy₂ heq
    rcases (hφ y₁ hy₁).2 with ⟨a₁, ha₁, rfl, hfa₁⟩
    rcases (hφ y₂ hy₂).2 with ⟨a₂, ha₂, rfl, hfa₂⟩
    exact hfg a₁ ha₁ a₂ ha₂ (hfa₁.trans (heq.trans hfa₂.symm))
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hs0
    simp

private theorem card_image_eq_of_eq_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) :
    (s.image f).card = (s.image g).card :=
  le_antisymm
    (card_image_le_of_eq_imp s g f (fun a ha b hb h1 => (h a ha b hb).mpr h1))
    (card_image_le_of_eq_imp s f g (fun a ha b hb h1 => (h a ha b hb).mp h1))

private theorem card_filter_split {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    s.card = (s.filter p).card + (s.filter (fun a => ¬ p a)).card := by
  have hun : s = s.filter p ∪ s.filter (fun a => ¬ p a) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hp : p a <;> simp [hp]
  have hdisj : Disjoint (s.filter p) (s.filter (fun a => ¬ p a)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  conv_lhs => rw [hun]
  exact Finset.card_union_of_disjoint hdisj

private theorem admissible_flip (d t n m : Nat) (G : Fin n → Fin m → Bool) (edge : Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) :
    admissible d t n m G edge R B ↔
    admissible d t n m (fun a c => G a c == edge) true R B := by
  have hbeq : ∀ (x y : Bool), ((x == edge) = (y == edge)) ↔ (x = y) := by
    intro x y; cases edge <;> cases x <;> cases y <;> decide
  have hrow_card :
      (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card =
      (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => (G inRow outCol == edge) = true))).card := by
    apply card_image_eq_of_eq_iff
    intro a _ b _
    constructor <;> intro h <;> ext c <;>
      have hc := Finset.ext_iff.mp h c <;>
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
    · constructor <;> rintro ⟨hcB, h1⟩ <;> refine ⟨hcB, ?_⟩
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
    · constructor <;> rintro ⟨hcB, h1⟩ <;> refine ⟨hcB, ?_⟩
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
      · cases edge <;> cases ha : G a c <;> cases hb : G b c <;> simp_all
  have hcol_card :
      (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card =
      (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => (G outRow inCol == edge) = true))).card := by
    apply card_image_eq_of_eq_iff
    intro a _ b _
    constructor <;> intro h <;> ext c <;>
      have hc := Finset.ext_iff.mp h c <;>
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
    · constructor <;> rintro ⟨hcR, h1⟩ <;> refine ⟨hcR, ?_⟩
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
    · constructor <;> rintro ⟨hcR, h1⟩ <;> refine ⟨hcR, ?_⟩
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
      · cases edge <;> cases ha : G c a <;> cases hb : G c b <;> simp_all
  have hnbrR : ∀ a,
      Finset.univ.filter (fun dest : Fin m => G a dest = edge) =
      Finset.univ.filter (fun dest : Fin m => (G a dest == edge) = true) := by
    intro a; ext c; simp [beq_iff_eq]
  have hnbrC : ∀ c,
      Finset.univ.filter (fun src : Fin n => G src c = edge) =
      Finset.univ.filter (fun src : Fin n => (G src c == edge) = true) := by
    intro c; ext a; simp [beq_iff_eq]
  unfold admissible
  dsimp only
  simp only [hnbrR, hnbrC, hrow_card, hcol_card]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, mark, hrect⟩
    refine ⟨h1, h2, h3, h4, h5, mark == edge, ?_⟩
    intro a ha b hb x hx y hy hax hbx hby
    have hcoreR : ∀ r, r ∈ R.filter (fun keptRow => ∃ w ∈ B, (G keptRow w == edge) ≠ (mark == edge)) →
        r ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ mark) := by
      intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      rcases hr with ⟨hrR, w, hwB, hne⟩
      exact ⟨hrR, w, hwB, fun h => hne (by rw [h])⟩
    have hcoreC : ∀ c, c ∈ B.filter (fun keptCol => ∃ w ∈ R, (G w keptCol == edge) ≠ (mark == edge)) →
        c ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ mark) := by
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hcB, w, hwR, hne⟩
      exact ⟨hcB, w, hwR, fun h => hne (by rw [h])⟩
    exact (hbeq (G a y) mark).mpr
      (hrect a (hcoreR a ha) b (hcoreR b hb) x (hcoreC x hx) y (hcoreC y hy)
        ((hbeq _ _).mp hax) ((hbeq _ _).mp hbx) ((hbeq _ _).mp hby))
  · rintro ⟨h1, h2, h3, h4, h5, mark, hrect⟩
    refine ⟨h1, h2, h3, h4, h5, mark == edge, ?_⟩
    have hinv : ∀ z : Bool, ((z == edge) == edge) = z := by
      intro z; cases edge <;> cases z <;> decide
    intro a ha b hb x hx y hy hax hbx hby
    have hcoreR : ∀ r, r ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ (mark == edge)) →
        r ∈ R.filter (fun keptRow => ∃ w ∈ B, (G keptRow w == edge) ≠ mark) := by
      intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      rcases hr with ⟨hrR, w, hwB, hne⟩
      exact ⟨hrR, w, hwB, fun h => hne (by rw [← h, hinv])⟩
    have hcoreC : ∀ c, c ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ (mark == edge)) →
        c ∈ B.filter (fun keptCol => ∃ w ∈ R, (G w keptCol == edge) ≠ mark) := by
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hcB, w, hwR, hne⟩
      exact ⟨hcB, w, hwR, fun h => hne (by rw [← h, hinv])⟩
    have hay := hrect a (hcoreR a ha) b (hcoreR b hb) x (hcoreC x hx) y (hcoreC y hy)
      (by rw [hax, hinv]) (by rw [hbx, hinv]) (by rw [hby, hinv])
    rw [← hay, hinv]

private theorem col_c4_of_row_c4 {n m : Nat} (G : Fin n → Fin m → Bool)
    (hrow : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (fun c : Fin m => G a c = true)) ∩
       (Finset.univ.filter (fun c : Fin m => G b c = true))).card ≤ 1) :
    ∀ x y : Fin m, x ≠ y →
      ((Finset.univ.filter (fun a : Fin n => G a x = true)) ∩
       (Finset.univ.filter (fun a : Fin n => G a y = true))).card ≤ 1 := by
  intro x y hxy
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hsub : ({x, y} : Finset (Fin m)) ⊆
      (Finset.univ.filter (fun c : Fin m => G a c = true)) ∩
      (Finset.univ.filter (fun c : Fin m => G b c = true)) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc with rfl | rfl
    · exact ⟨ha.1, hb.1⟩
    · exact ⟨ha.2, hb.2⟩
  have h2 : 2 ≤ ({x, y} : Finset (Fin m)).card := by
    rw [Finset.card_pair hxy]
  have hle := Finset.card_le_card hsub
  have h1 := hrow a b hab
  omega

private theorem admissible_transpose (d t n m : Nat) (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) :
    admissible d t n m G true R B →
    admissible d t m n (fun c a => G a c) true B R := by
  rintro ⟨h1, h2, h3, h4, h5, mark, hrect⟩
  refine ⟨h2, h1, col_c4_of_row_c4 G h3, h5, h4, mark, ?_⟩
  intro x hx y hy a ha b hb hxa hya hyb
  exact hrect b hb a ha y hy x hx hyb hya hxa

private theorem card_le_mul_of_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (k M : Nat)
    (him : (s.image f).card ≤ k)
    (hfib : ∀ y ∈ s.image f, (s.filter (fun a => f a = y)).card ≤ M) :
    s.card ≤ k * M := by
  have heq : s.card = ∑ y ∈ s.image f, (s.filter (fun a => f a = y)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := s.image f)]
    intro a ha
    exact Finset.mem_image_of_mem f ha
  rw [heq]
  calc ∑ y ∈ s.image f, (s.filter (fun a => f a = y)).card
      ≤ ∑ _y ∈ s.image f, M := Finset.sum_le_sum (fun y hy => hfib y hy)
    _ = (s.image f).card * M := by simp
    _ ≤ k * M := Nat.mul_le_mul_right M him

private theorem card_le_dt_of_empty_le_d {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) (d t : Nat)
    (him : (s.image f).card ≤ t)
    (hnonempty_fib : ∀ P : Finset β, P.Nonempty → (s.filter (fun a => f a = P)).card ≤ d)
    (h0 : (s.filter (fun a => f a = ∅)).card ≤ d) :
    s.card ≤ d * t := by
  let s0 := s.filter (fun a => f a = ∅)
  let s1 := s.filter (fun a => f a ≠ ∅)
  have h0' : s0.card ≤ d := h0
  have hsum : s.card = s0.card + s1.card := card_filter_split s (fun a => f a = ∅)
  by_cases h0ne : s0.Nonempty
  · have hmem0 : (∅ : Finset β) ∈ s.image f := by
      rcases h0ne with ⟨a, ha⟩
      exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
    have hsub : s1.image f ⊆ (s.image f).erase ∅ := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
      rcases Finset.mem_filter.mp ha with ⟨has, hne⟩
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f has⟩
    have him1 : (s1.image f).card ≤ t - 1 := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hmem0] at h1
      omega
    have hs1 : s1.card ≤ (t - 1) * d := by
      apply card_le_mul_of_fiber_bound s1 f (t - 1) d him1
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
      have hPne : (f a).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp ha).2
      calc (s1.filter (fun x => f x = f a)).card
          ≤ (s.filter (fun x => f x = f a)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [s1, Finset.mem_filter] at hx ⊢
            exact ⟨hx.1.1, hx.2⟩
        _ ≤ d := hnonempty_fib (f a) hPne
    have hdt : d + (t - 1) * d ≤ d * t := by
      cases t with
      | zero =>
        have hpos : 0 < (s.image f).card := Finset.card_pos.mpr ⟨∅, hmem0⟩
        omega
      | succ t' =>
        simp only [Nat.add_sub_cancel]
        rw [Nat.mul_comm t' d, Nat.mul_succ, Nat.add_comm]
    omega
  · have hs0 : s0.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h0ne)
    have hs1 : s1.card ≤ t * d := by
      apply card_le_mul_of_fiber_bound s1 f t d
      · exact (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))).trans him
      · intro P hP
        rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
        have hPne : (f a).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp ha).2
        calc (s1.filter (fun x => f x = f a)).card
            ≤ (s.filter (fun x => f x = f a)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [s1, Finset.mem_filter] at hx ⊢
              exact ⟨hx.1.1, hx.2⟩
          _ ≤ d := hnonempty_fib (f a) hPne
    rw [Nat.mul_comm] at hs1
    omega

private theorem upper_bound_one_empty_side (d t n m : Nat) (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m))
    (hd : 2 ≤ d) (ht : 2 ≤ t)
    (hnbrR : ∀ a : Fin n, 2 ≤ (Finset.univ.filter (fun c : Fin m => G a c = true)).card ∧
      (Finset.univ.filter (fun c : Fin m => G a c = true)).card ≤ d)
    (hnbrC : ∀ c : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => G a c = true)).card ∧
      (Finset.univ.filter (fun a : Fin n => G a c = true)).card ≤ d)
    (hc4R : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (fun c : Fin m => G a c = true)) ∩
       (Finset.univ.filter (fun c : Fin m => G b c = true))).card ≤ 1)
    (hrowT : (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤ t)
    (hcolT : (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤ t)
    (hrect : ∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
      G a x = true → G b x = true → G b y = true → G a y = true)
    (hR0_empty : R.filter (fun a => (Finset.univ \ B).filter (fun c => G a c = true) = ∅) = ∅)
    (hB0_ne : (B.filter (fun c => (Finset.univ \ R).filter (fun a => G a c = true) = ∅)).Nonempty) :
    R.card + B.card ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := by
  let nbrR := fun a : Fin n => Finset.univ.filter (fun c : Fin m => G a c = true)
  let nbrC := fun c : Fin m => Finset.univ.filter (fun a : Fin n => G a c = true)
  let extR := fun a : Fin n => (Finset.univ \ B).filter (fun c : Fin m => G a c = true)
  let extC := fun c : Fin m => (Finset.univ \ R).filter (fun a : Fin n => G a c = true)
  let B0 := B.filter (fun c => extC c = ∅)
  let B1 := B.filter (fun c => extC c ≠ ∅)
  have h2dt : 2 * d * t = d * t + d * t := by rw [Nat.two_mul, Nat.add_mul]
  change ∀ a : Fin n, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d at hnbrR
  change ∀ c : Fin m, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d at hnbrC
  change ∀ a b : Fin n, a ≠ b → (nbrR a ∩ nbrR b).card ≤ 1 at hc4R
  change (R.image extR).card ≤ t at hrowT
  change (B.image extC).card ≤ t at hcolT
  have hc4C : ∀ x y : Fin m, x ≠ y → (nbrC x ∩ nbrC y).card ≤ 1 := col_c4_of_row_c4 G hc4R
  have hBsum : B.card = B0.card + B1.card := card_filter_split B (fun c => extC c = ∅)
  have hfibR : ∀ P : Finset (Fin m), P.Nonempty → (R.filter (fun a => extR a = P)).card ≤ d := by
    rintro P ⟨c0, hc0⟩
    have hsub : R.filter (fun a => extR a = P) ⊆ nbrC c0 := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨_, hP⟩
      have hc0' : c0 ∈ extR a := hP ▸ hc0
      simp only [extR, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc0' ⊢
      exact hc0'.2
    exact (Finset.card_le_card hsub).trans (hnbrC c0).2
  have hfibB : ∀ P : Finset (Fin n), P.Nonempty → (B.filter (fun c => extC c = P)).card ≤ d := by
    rintro P ⟨a0, ha0⟩
    have hsub : B.filter (fun c => extC c = P) ⊆ nbrR a0 := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨_, hP⟩
      have ha0' : a0 ∈ extC c := hP ▸ ha0
      simp only [extC, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha0' ⊢
      exact ha0'.2
    exact (Finset.card_le_card hsub).trans (hnbrR a0).2
  have hR_le_dt : R.card ≤ d * t := by
    apply card_le_dt_of_empty_le_d R extR d t hrowT hfibR
    rw [hR0_empty]; simp
  have hB0_sub_R : ∀ x ∈ B0, nbrC x ⊆ R := by
    intro x hx a ha
    have hxe : extC x = ∅ := (Finset.mem_filter.mp hx).2
    by_contra haR
    have hmem : a ∈ extC x := by
      simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
      exact ⟨haR, ha⟩
    rw [hxe] at hmem; simp at hmem
  have hstar_B0 : ∀ x ∈ B0, ∀ a ∈ nbrC x, ∀ y ∈ B, G a y = true → y = x := by
    intro x hx a ha y hy hay
    have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
    have haR : a ∈ R := hB0_sub_R x hx ha
    by_contra hyx
    have hcard : 2 ≤ (nbrC x).card := (hnbrC x).1
    have hne : ((nbrC x).erase a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hem
      have h1 : (nbrC x).card ≤ 1 := by
        have := Finset.card_erase_of_mem ha
        rw [hem] at this; simp at this; omega
      omega
    rcases hne with ⟨b, hb⟩
    rcases Finset.mem_erase.mp hb with ⟨hba, hbN⟩
    have hbR : b ∈ R := hB0_sub_R x hx hbN
    have hax : G a x = true := (Finset.mem_filter.mp ha).2
    have hbx : G b x = true := (Finset.mem_filter.mp hbN).2
    have hby : G b y = true := hrect b hbR a haR x hxB y hy hbx hax hay
    have hsub : ({a, b} : Finset (Fin n)) ⊆ nbrC x ∩ nbrC y := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      simp only [nbrC, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hr with rfl | rfl
      · exact ⟨hax, hay⟩
      · exact ⟨hbx, hby⟩
    have hpair : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hba)
    have h1 := hc4C x y (Ne.symm hyx)
    have hle := Finset.card_le_card hsub
    omega
  let Rused := B0.biUnion (fun x => nbrC x)
  have hRused_sub : Rused ⊆ R := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨x, hx, hax⟩
    exact hB0_sub_R x hx hax
  have hRused_disj : Set.PairwiseDisjoint (B0 : Set (Fin m)) (fun x => nbrC x) := by
    intro x hx y hy hxy
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a hax hay
    have hyB : y ∈ B := (Finset.mem_filter.mp hy).1
    have hgay : G a y = true := (Finset.mem_filter.mp hay).2
    exact hxy (hstar_B0 x hx a hax y hyB hgay).symm
  have h2B0_le_Rused : 2 * B0.card ≤ Rused.card := by
    rw [Finset.card_biUnion hRused_disj]
    calc 2 * B0.card = ∑ _x ∈ B0, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ B0, (nbrC x).card := Finset.sum_le_sum (fun x _ => (hnbrC x).1)
  have hRused_le_R : Rused.card ≤ R.card := Finset.card_le_card hRused_sub
  have hB1_im_le : (B1.image extC).card ≤ t - 1 := by
    have hmem0 : (∅ : Finset (Fin n)) ∈ B.image extC := by
      rcases hB0_ne with ⟨x, hx⟩
      exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hsub : B1.image extC ⊆ (B.image extC).erase ∅ := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
      rcases Finset.mem_filter.mp hc with ⟨hcB, hne⟩
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem extC hcB⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem0] at hle
    omega
  by_cases hB1_empty : B1 = ∅
  · have hB1c : B1.card = 0 := Finset.card_eq_zero.mpr hB1_empty
    have hcap1 : 2 * d * t ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := le_max_left _ _
    omega
  · have hB1ne : (B1.image extC).Nonempty :=
      Finset.Nonempty.image (Finset.nonempty_iff_ne_empty.mpr hB1_empty) extC
    rcases Finset.exists_max_image (B1.image extC) (fun P => (B1.filter (fun c => extC c = P)).card) hB1ne
      with ⟨Pmax, hPmax_mem, hPmax_max⟩
    let Dmax := B1.filter (fun c => extC c = Pmax)
    let h := Dmax.card
    have hB1_le_th : B1.card ≤ (t - 1) * h :=
      card_le_mul_of_fiber_bound B1 extC (t - 1) h hB1_im_le hPmax_max
    have hh_le_d : h ≤ d := by
      rcases Finset.mem_image.mp hPmax_mem with ⟨c0, hc0, rfl⟩
      have hPne : (extC c0).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hc0).2
      calc Dmax.card ≤ (B.filter (fun c => extC c = extC c0)).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Dmax, B1, Finset.mem_filter] at hc ⊢
            exact ⟨hc.1.1, hc.2⟩
        _ ≤ d := hfibB (extC c0) hPne
    by_cases hh1 : h ≤ 1
    · have hB1_le : B1.card ≤ t - 1 := by
        calc B1.card ≤ (t - 1) * h := hB1_le_th
          _ ≤ (t - 1) * 1 := Nat.mul_le_mul_left (t - 1) hh1
          _ = t - 1 := Nat.mul_one _
      have hdt_ge : 2 * (t - 1) ≤ d * t := by
        have h1 : 2 * (t - 1) ≤ 2 * t := by omega
        have h2 : 2 * t ≤ d * t := Nat.mul_le_mul_right t hd
        omega
      have hcap1 : 2 * d * t ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := le_max_left _ _
      omega
    · have hh2 : 2 ≤ h := by omega
      rcases Finset.one_lt_card.mp (by omega : 1 < Dmax.card) with ⟨c₁, hc₁, c₂, hc₂, hc12⟩
      have hext_eq : extC c₁ = Pmax ∧ extC c₂ = Pmax :=
        ⟨(Finset.mem_filter.mp hc₁).2, (Finset.mem_filter.mp hc₂).2⟩
      have hPmax_ne : Pmax.Nonempty := by
        rw [← hext_eq.1]
        exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hc₁).1).2
      have hPmax_card_le : Pmax.card ≤ 1 := by
        have hsub : Pmax ⊆ nbrC c₁ ∩ nbrC c₂ := by
          intro a ha
          have ha1 : a ∈ extC c₁ := hext_eq.1.symm ▸ ha
          have ha2 : a ∈ extC c₂ := hext_eq.2.symm ▸ ha
          simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_inter] at ha1 ha2 ⊢
          exact ⟨ha1.2, ha2.2⟩
        exact (Finset.card_le_card hsub).trans (hc4C c₁ c₂ hc12)
      rcases hPmax_ne with ⟨r_ext, hr_ext⟩
      have hr_ext_notR : r_ext ∉ R := by
        have hmem : r_ext ∈ extC c₁ := hext_eq.1.symm ▸ hr_ext
        simp only [extC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hmem
        exact hmem.1
      have hD_has_R : ∀ c ∈ Dmax, (nbrC c ∩ R).Nonempty := by
        intro c hc
        have hcext : extC c = Pmax := (Finset.mem_filter.mp hc).2
        have hpart : nbrC c ⊆ (nbrC c ∩ R) ∪ extC c := by
          intro a ha
          by_cases haR : a ∈ R
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, haR⟩)
          · apply Finset.mem_union_right
            simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
            exact ⟨haR, ha⟩
        have hle := Finset.card_le_card hpart
        have hun := Finset.card_union_le (nbrC c ∩ R) (extC c)
        have h2 := (hnbrC c).1
        rw [hcext] at hle hun
        have hpos : 0 < (nbrC c ∩ R).card := by omega
        exact Finset.card_pos.mp hpos
      have hchoose : ∀ c : Fin m, ∃ a : Fin n, c ∈ Dmax → a ∈ nbrC c ∩ R := by
        intro c
        by_cases hc : c ∈ Dmax
        · rcases hD_has_R c hc with ⟨a, ha⟩
          exact ⟨a, fun _ => ha⟩
        · exact ⟨r_ext, fun h1 => absurd h1 hc⟩
      choose f hf using hchoose
      have hf_inj : Set.InjOn f (Dmax : Set (Fin m)) := by
        intro x hx y hy hfeq
        by_contra hxy
        have hfx := hf x hx
        have hfy := hf y hy
        rw [← hfeq] at hfy
        have hfxR : f x ∈ R := (Finset.mem_inter.mp hfx).2
        have hre_x : r_ext ∈ nbrC x := by
          have hm : r_ext ∈ extC x := (Finset.mem_filter.mp hx).2.symm ▸ hr_ext
          simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
          exact hm.2
        have hre_y : r_ext ∈ nbrC y := by
          have hm : r_ext ∈ extC y := (Finset.mem_filter.mp hy).2.symm ▸ hr_ext
          simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm ⊢
          exact hm.2
        have hne_fr : f x ≠ r_ext := fun heq => hr_ext_notR (heq ▸ hfxR)
        have hsub : ({f x, r_ext} : Finset (Fin n)) ⊆ nbrC x ∩ nbrC y := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hfx).1, (Finset.mem_inter.mp hfy).1⟩
          · exact Finset.mem_inter.mpr ⟨hre_x, hre_y⟩
        have hpair : ({f x, r_ext} : Finset (Fin n)).card = 2 := Finset.card_pair hne_fr
        have hle := Finset.card_le_card hsub
        have h1 := hc4C x y hxy
        omega
      have hf_disj : Disjoint (Dmax.image f) Rused := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        rcases Finset.mem_image.mp ha1 with ⟨c, hcD, rfl⟩
        rcases Finset.mem_biUnion.mp ha2 with ⟨x, hx0, hax⟩
        have hcB1 : c ∈ B1 := (Finset.mem_filter.mp hcD).1
        have hcB : c ∈ B := (Finset.mem_filter.mp hcB1).1
        have hfc : G (f c) c = true := (Finset.mem_filter.mp (Finset.mem_inter.mp (hf c hcD)).1).2
        have hcx : c = x := hstar_B0 x hx0 (f c) hax c hcB hfc
        subst hcx
        exact (Finset.mem_filter.mp hcB1).2 (Finset.mem_filter.mp hx0).2
      have hf_sub : Dmax.image f ⊆ R := by
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨c, hcD, rfl⟩
        exact (Finset.mem_inter.mp (hf c hcD)).2
      have hR_ge : Rused.card + h ≤ R.card := by
        have h1 : (Dmax.image f ∪ Rused).card ≤ R.card :=
          Finset.card_le_card (Finset.union_subset hf_sub hRused_sub)
        rw [Finset.card_union_of_disjoint hf_disj, Finset.card_image_of_injOn hf_inj] at h1
        omega
      have h2B0_le : 2 * B0.card + h ≤ R.card := by omega
      have h2sum : 2 * (R.card + B.card) ≤ d * (5 * t - 3) := by
        have h1 : 2 * (R.card + B.card) ≤ 3 * R.card + (2 * t - 3) * h := by
          have h2 : 2 * ((t - 1) * h) = (2 * t - 2) * h := by
            cases t with
            | zero => omega
            | succ t' =>
              simp only [Nat.add_sub_cancel]
              have hEq : 2 * (t' + 1) - 2 = 2 * t' := by omega
              rw [hEq, Nat.mul_assoc]
          have h3 : (2 * t - 2) * h = (2 * t - 3) * h + h := by
            have hEq : 2 * t - 2 = (2 * t - 3) + 1 := by omega
            rw [hEq, Nat.add_mul, Nat.one_mul]
          omega
        have h2 : 3 * R.card ≤ 3 * (d * t) := Nat.mul_le_mul_left 3 hR_le_dt
        have h3 : (2 * t - 3) * h ≤ (2 * t - 3) * d := Nat.mul_le_mul_left (2 * t - 3) hh_le_d
        have h4 : 3 * (d * t) + (2 * t - 3) * d = d * (5 * t - 3) := by
          have hEq : 3 * t + (2 * t - 3) = 5 * t - 3 := by omega
          calc 3 * (d * t) + (2 * t - 3) * d
              = d * (3 * t) + d * (2 * t - 3) := by rw [Nat.mul_left_comm, Nat.mul_comm (2 * t - 3) d]
            _ = d * (3 * t + (2 * t - 3)) := by rw [← Nat.mul_add]
            _ = d * (5 * t - 3) := by rw [hEq]
        omega
      by_cases ht3 : t ≤ 3
      · have h54 : 5 * t - 3 ≤ 4 * t := by omega
        have hbound : d * (5 * t - 3) ≤ 2 * (2 * d * t) := by
          calc d * (5 * t - 3) ≤ d * (4 * t) := Nat.mul_le_mul_left d h54
            _ = 2 * (2 * d * t) := by
              rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm d 4]
              have : 4 * d = 2 * (2 * d) := by omega
              rw [this, Nat.mul_assoc]
        have hcap1 : 2 * d * t ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := le_max_left _ _
        omega
      · have ht4 : 4 ≤ t := by omega
        let L := d * (t - 1)
        have hdiv : 2 * (L / 2) + 1 ≥ L := by omega
        have hdt_ge : 2 ≤ d * (t - 3) := by
          have h1 : 1 ≤ t - 3 := by omega
          calc 2 = 2 * 1 := by simp
            _ ≤ d * (t - 3) := Nat.mul_le_mul hd h1
        have hbound : d * (5 * t - 3) ≤ 6 * L - 2 := by
          have hEq : 6 * L = d * (6 * t - 6) := by
            have h6 : 6 * (t - 1) = 6 * t - 6 := by omega
            calc 6 * (d * (t - 1)) = d * (6 * (t - 1)) := Nat.mul_left_comm 6 d (t - 1)
              _ = d * (6 * t - 6) := by rw [h6]
          have hEq2 : d * (6 * t - 6) = d * (5 * t - 3) + d * (t - 3) := by
            rw [← Nat.mul_add]
            congr 1
            omega
          omega
        have hcap2 : 2 * L + 2 * (L / 2) ≤ max (2 * d * t) (2 * L + 2 * (L / 2)) := le_max_right _ _
        omega

private theorem upper_bound_true (d t n m : Nat) (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m))
    (hd : 2 ≤ d) (ht : 2 ≤ t)
    (hadm : admissible d t n m G true R B) :
    R.card + B.card ≤ max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := by
  let L := d * (t - 1)
  let cap := max (2 * d * t) (2 * L + 2 * (L / 2))
  have hcap1 : 2 * d * t ≤ cap := le_max_left _ _
  have hcap2 : 2 * L + 2 * (L / 2) ≤ cap := le_max_right _ _
  have h2dt : 2 * d * t = d * t + d * t := by rw [Nat.two_mul, Nat.add_mul]
  rcases hadm with ⟨hnbrR, hnbrC, hc4R, hrowT, hcolT, mark, hrect⟩
  let nbrR := fun a : Fin n => Finset.univ.filter (fun c : Fin m => G a c = true)
  let nbrC := fun c : Fin m => Finset.univ.filter (fun a : Fin n => G a c = true)
  let extR := fun a : Fin n => (Finset.univ \ B).filter (fun c : Fin m => G a c = true)
  let extC := fun c : Fin m => (Finset.univ \ R).filter (fun a : Fin n => G a c = true)
  change ∀ a : Fin n, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d at hnbrR
  change ∀ c : Fin m, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d at hnbrC
  change ∀ a b : Fin n, a ≠ b → (nbrR a ∩ nbrR b).card ≤ 1 at hc4R
  change (R.image extR).card ≤ t at hrowT
  change (B.image extC).card ≤ t at hcolT
  have hc4C : ∀ x y : Fin m, x ≠ y → (nbrC x ∩ nbrC y).card ≤ 1 := col_c4_of_row_c4 G hc4R
  let R0 := R.filter (fun a => extR a = ∅)
  let R1 := R.filter (fun a => extR a ≠ ∅)
  let B0 := B.filter (fun c => extC c = ∅)
  let B1 := B.filter (fun c => extC c ≠ ∅)
  have hRsum : R.card = R0.card + R1.card := card_filter_split R (fun a => extR a = ∅)
  have hBsum : B.card = B0.card + B1.card := card_filter_split B (fun c => extC c = ∅)
  have hfibR : ∀ P : Finset (Fin m), P.Nonempty → (R.filter (fun a => extR a = P)).card ≤ d := by
    rintro P ⟨c0, hc0⟩
    have hsub : R.filter (fun a => extR a = P) ⊆ nbrC c0 := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨_, hP⟩
      have hc0' : c0 ∈ extR a := hP ▸ hc0
      simp only [extR, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc0' ⊢
      exact hc0'.2
    exact (Finset.card_le_card hsub).trans (hnbrC c0).2
  have hfibB : ∀ P : Finset (Fin n), P.Nonempty → (B.filter (fun c => extC c = P)).card ≤ d := by
    rintro P ⟨a0, ha0⟩
    have hsub : B.filter (fun c => extC c = P) ⊆ nbrR a0 := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨_, hP⟩
      have ha0' : a0 ∈ extC c := hP ▸ ha0
      simp only [extC, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha0' ⊢
      exact ha0'.2
    exact (Finset.card_le_card hsub).trans (hnbrR a0).2
  have hR_le_dt : R0.card ≤ d → R.card ≤ d * t :=
    fun h => card_le_dt_of_empty_le_d R extR d t hrowT hfibR h
  have hB_le_dt : B0.card ≤ d → B.card ≤ d * t :=
    fun h => card_le_dt_of_empty_le_d B extC d t hcolT hfibB h
  have hR0_sub_B : ∀ a ∈ R0, nbrR a ⊆ B := by
    intro a ha c hc
    have hae : extR a = ∅ := (Finset.mem_filter.mp ha).2
    by_contra hcB
    have hmem : c ∈ extR a := by
      simp only [extR, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨hcB, hc⟩
    rw [hae] at hmem; simp at hmem
  have hB0_sub_R : ∀ c ∈ B0, nbrC c ⊆ R := by
    intro c hc a ha
    have hce : extC c = ∅ := (Finset.mem_filter.mp hc).2
    by_contra haR
    have hmem : a ∈ extC c := by
      simp only [extC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
      exact ⟨haR, ha⟩
    rw [hce] at hmem; simp at hmem
  cases mark
  · let cR := R.filter (fun a => ∃ x ∈ B, G a x ≠ false)
    let cB := B.filter (fun x => ∃ a ∈ R, G a x ≠ false)
    have hR0_sub_cR : R0 ⊆ cR := by
      intro a ha
      have haR : a ∈ R := (Finset.mem_filter.mp ha).1
      have hne : (nbrR a).Nonempty := Finset.card_pos.mp (by have := (hnbrR a).1; omega)
      rcases hne with ⟨x, hx⟩
      refine Finset.mem_filter.mpr ⟨haR, x, hR0_sub_B a ha hx, ?_⟩
      have hG : G a x = true := (Finset.mem_filter.mp hx).2
      rw [hG]; decide
    have hB0_sub_cB : B0 ⊆ cB := by
      intro x hx
      have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
      have hne : (nbrC x).Nonempty := Finset.card_pos.mp (by have := (hnbrC x).1; omega)
      rcases hne with ⟨a, ha⟩
      refine Finset.mem_filter.mpr ⟨hxB, a, hB0_sub_R x hx ha, ?_⟩
      have hG : G a x = true := (Finset.mem_filter.mp ha).2
      rw [hG]; decide
    have hnonedge_eq : ∀ a ∈ cR, ∀ b ∈ cR,
        (∃ x ∈ cB, G a x = false ∧ G b x = false) → nbrR a ∩ cB = nbrR b ∩ cB := by
      intro a ha b hb ⟨x, hx, hax, hbx⟩
      ext y
      simp only [nbrR, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> rintro ⟨hG, hy⟩ <;> refine ⟨?_, hy⟩
      · cases hby : G b y
        · have hay := hrect a ha b hb x hx y hy hax hbx hby
          rw [hay] at hG; cases hG
        · rfl
      · cases hay : G a y
        · have hby := hrect b hb a ha x hx y hy hbx hax hay
          rw [hby] at hG; cases hG
        · rfl
    have hB0_le1_of_cR_le2 : cR.card ≤ 2 → B0.card ≤ 1 := by
      intro hcR2
      rw [Finset.card_le_one]
      intro x hx y hy
      by_contra hxy
      have hxsub : nbrC x ⊆ cR := by
        intro a ha
        have haR := hB0_sub_R x hx ha
        have hG : G a x = true := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨haR, x, (Finset.mem_filter.mp hx).1, by rw [hG]; decide⟩
      have hysub : nbrC y ⊆ cR := by
        intro a ha
        have haR := hB0_sub_R y hy ha
        have hG : G a y = true := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨haR, y, (Finset.mem_filter.mp hy).1, by rw [hG]; decide⟩
      have hxeq : nbrC x = cR := Finset.eq_of_subset_of_card_le hxsub (by have := (hnbrC x).1; omega)
      have hyeq : nbrC y = cR := Finset.eq_of_subset_of_card_le hysub (by have := (hnbrC y).1; omega)
      have hinter : (nbrC x ∩ nbrC y).card = cR.card := by rw [hxeq, hyeq, Finset.inter_self]
      have h1 := hc4C x y hxy
      have h2 := (hnbrC x).1
      rw [hxeq] at h2
      omega
    have hR0_le1_of_cB_le2 : cB.card ≤ 2 → R0.card ≤ 1 := by
      intro hcB2
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      have hasub : nbrR a ⊆ cB := by
        intro x hx
        have hxB := hR0_sub_B a ha hx
        have hG : G a x = true := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨hxB, a, (Finset.mem_filter.mp ha).1, by rw [hG]; decide⟩
      have hbsub : nbrR b ⊆ cB := by
        intro x hx
        have hxB := hR0_sub_B b hb hx
        have hG : G b x = true := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨hxB, b, (Finset.mem_filter.mp hb).1, by rw [hG]; decide⟩
      have haeq : nbrR a = cB := Finset.eq_of_subset_of_card_le hasub (by have := (hnbrR a).1; omega)
      have hbeq : nbrR b = cB := Finset.eq_of_subset_of_card_le hbsub (by have := (hnbrR b).1; omega)
      have hinter : (nbrR a ∩ nbrR b).card = cB.card := by rw [haeq, hbeq, Finset.inter_self]
      have h1 := hc4R a b hab
      have h2 := (hnbrR a).1
      rw [haeq] at h2
      omega
    by_cases hcR2 : cR.card ≤ 2
    · have hR0le : R0.card ≤ d := (Finset.card_le_card hR0_sub_cR).trans (by omega)
      have hB0le : B0.card ≤ d := (hB0_le1_of_cR_le2 hcR2).trans (by omega)
      have h1 := hR_le_dt hR0le
      have h2 := hB_le_dt hB0le
      omega
    · have hcR3 : 3 ≤ cR.card := by omega
      by_cases hexV : ∃ a ∈ cR, 2 ≤ (cB \ nbrR a).card
      · rcases hexV with ⟨a0, ha0, hV2⟩
        let V := cB \ nbrR a0
        change 2 ≤ V.card at hV2
        let U := cR.filter (fun b => nbrR b ∩ cB = nbrR a0 ∩ cB)
        have hV_sub : ∀ b ∈ cR \ U, V ⊆ nbrR b := by
          intro b hb x hx
          rcases Finset.mem_sdiff.mp hb with ⟨hbcR, hbnU⟩
          rcases Finset.mem_sdiff.mp hx with ⟨hxcB, hxna0⟩
          have ha0x : G a0 x = false := by
            cases hG : G a0 x
            · rfl
            · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hG⟩) hxna0
          cases hbx : G b x
          · exfalso
            apply hbnU
            exact Finset.mem_filter.mpr ⟨hbcR, hnonedge_eq b hbcR a0 ha0 ⟨x, hxcB, hbx, ha0x⟩⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩
        have hrest_le1 : (cR \ U).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro b₁ hb₁ b₂ hb₂
          by_contra h12
          have hsub : V ⊆ nbrR b₁ ∩ nbrR b₂ :=
            Finset.subset_inter (hV_sub b₁ hb₁) (hV_sub b₂ hb₂)
          have hle := Finset.card_le_card hsub
          have h1 := hc4R b₁ b₂ h12
          omega
        have hU_ge2 : 2 ≤ U.card := by
          have hsub : U ⊆ cR := Finset.filter_subset _ _
          have hsd := Finset.card_sdiff_add_card_eq_card hsub
          omega
        rcases Finset.one_lt_card.mp (by omega : 1 < U.card) with ⟨a₁, ha₁, a₂, ha₂, ha12⟩
        have ha1eq : nbrR a₁ ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp ha₁).2
        have ha2eq : nbrR a₂ ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp ha₂).2
        have hN_le1 : (nbrR a0 ∩ cB).card ≤ 1 := by
          have hsub : nbrR a0 ∩ cB ⊆ nbrR a₁ ∩ nbrR a₂ := by
            intro x hx
            have h1 : x ∈ nbrR a₁ ∩ cB := ha1eq.symm ▸ hx
            have h2 : x ∈ nbrR a₂ ∩ cB := ha2eq.symm ▸ hx
            exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩
          exact (Finset.card_le_card hsub).trans (hc4R a₁ a₂ ha12)
        have hR0_le1 : R0.card ≤ 1 := by
          have hsub : R0 ⊆ cR \ U := by
            intro r hr
            have hrcR : r ∈ cR := hR0_sub_cR hr
            refine Finset.mem_sdiff.mpr ⟨hrcR, ?_⟩
            intro hrU
            have hreq : nbrR r ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp hrU).2
            have hsub2 : nbrR r ⊆ nbrR r ∩ cB := by
              intro x hx
              have hxB : x ∈ B := hR0_sub_B r hr hx
              have hG : G r x = true := (Finset.mem_filter.mp hx).2
              exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨hxB, r, (Finset.mem_filter.mp hr).1, by rw [hG]; decide⟩⟩
            have hle := Finset.card_le_card hsub2
            rw [hreq] at hle
            have h2 := (hnbrR r).1
            omega
          exact (Finset.card_le_card hsub).trans hrest_le1
        have hB0_le1 : B0.card ≤ 1 := by
          have hsub : B0 ⊆ nbrR a0 ∩ cB := by
            intro x hx
            have hxcB : x ∈ cB := hB0_sub_cB hx
            by_contra hxn
            have hxV : x ∈ V := by
              refine Finset.mem_sdiff.mpr ⟨hxcB, ?_⟩
              intro hxna
              exact hxn (Finset.mem_inter.mpr ⟨hxna, hxcB⟩)
            have hnx_sub : nbrC x ⊆ cR \ U := by
              intro r hr
              have hrR : r ∈ R := hB0_sub_R x hx hr
              have hG : G r x = true := (Finset.mem_filter.mp hr).2
              have hrcR : r ∈ cR := Finset.mem_filter.mpr ⟨hrR, x, (Finset.mem_filter.mp hx).1, by rw [hG]; decide⟩
              refine Finset.mem_sdiff.mpr ⟨hrcR, ?_⟩
              intro hrU
              have hreq : nbrR r ∩ cB = nbrR a0 ∩ cB := (Finset.mem_filter.mp hrU).2
              have hmem : x ∈ nbrR a0 ∩ cB := by
                rw [← hreq]
                exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩, hxcB⟩
              exact hxn hmem
            have hle := (Finset.card_le_card hnx_sub).trans hrest_le1
            have h2 := (hnbrC x).1
            omega
          exact (Finset.card_le_card hsub).trans hN_le1
        have h1 := hR_le_dt (by omega)
        have h2 := hB_le_dt (by omega)
        omega
      · have hallV : ∀ a ∈ cR, (cB \ nbrR a).card ≤ 1 := by
          intro a ha
          by_contra hgt
          exact hexV ⟨a, ha, by omega⟩
        rcases Finset.one_lt_card.mp (by omega : 1 < cR.card) with ⟨a₁, ha₁, a₂, ha₂, ha12⟩
        have hcB_le3 : cB.card ≤ 3 := by
          have hsub : cB ⊆ (cB \ nbrR a₁) ∪ (cB \ nbrR a₂) ∪ (nbrR a₁ ∩ nbrR a₂) := by
            intro x hx
            by_cases h1 : x ∈ nbrR a₁
            · by_cases h2 : x ∈ nbrR a₂
              · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h1, h2⟩)
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, h2⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h1⟩))
          have hle := Finset.card_le_card hsub
          have hu1 := Finset.card_union_le ((cB \ nbrR a₁) ∪ (cB \ nbrR a₂)) (nbrR a₁ ∩ nbrR a₂)
          have hu2 := Finset.card_union_le (cB \ nbrR a₁) (cB \ nbrR a₂)
          have hv1 := hallV a₁ ha₁
          have hv2 := hallV a₂ ha₂
          have hi := hc4R a₁ a₂ ha12
          omega
        by_cases hcB2 : cB.card ≤ 2
        · have hR0le : R0.card ≤ d := (hR0_le1_of_cB_le2 hcB2).trans (by omega)
          have hB0le : B0.card ≤ d := (Finset.card_le_card hB0_sub_cB).trans (by omega)
          have h1 := hR_le_dt hR0le
          have h2 := hB_le_dt hB0le
          omega
        · have hcB3 : cB.card = 3 := by omega
          have hdeg_cR : ∀ a ∈ cR, (nbrR a ∩ cB).card = 2 := by
            intro a ha
            have hpart : (nbrR a ∩ cB).card + (cB \ nbrR a).card = cB.card := by
              have h := Finset.card_sdiff_add_card_inter cB (nbrR a)
              rw [Finset.inter_comm] at h
              exact Nat.add_comm _ _ ▸ h
            have hv := hallV a ha
            have hge2 : 2 ≤ (nbrR a ∩ cB).card := by omega
            have hle2 : (nbrR a ∩ cB).card ≤ 2 := by
              by_contra h3
              have hfull : nbrR a ∩ cB = cB :=
                Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by omega)
              have hne : (cR.erase a).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hem
                have h1 := Finset.card_erase_of_mem ha
                rw [hem] at h1; simp at h1; omega
              rcases hne with ⟨b, hb⟩
              rcases Finset.mem_erase.mp hb with ⟨hba, hbcR⟩
              have hbpart : (nbrR b ∩ cB).card + (cB \ nbrR b).card = cB.card := by
                have h := Finset.card_sdiff_add_card_inter cB (nbrR b)
                rw [Finset.inter_comm] at h
                exact Nat.add_comm _ _ ▸ h
              have hvb := hallV b hbcR
              have hsub : nbrR b ∩ cB ⊆ nbrR a ∩ nbrR b := by
                intro x hx
                have hxcB : x ∈ cB := (Finset.mem_inter.mp hx).2
                have hxa : x ∈ nbrR a := (Finset.mem_inter.mp (hfull.symm ▸ hxcB)).1
                exact Finset.mem_inter.mpr ⟨hxa, (Finset.mem_inter.mp hx).1⟩
              have hle := Finset.card_le_card hsub
              have hi := hc4R a b (Ne.symm hba)
              omega
            omega
          have hcR_le3 : cR.card ≤ 3 := by
            have hmiss_card : ∀ a ∈ cR, (cB \ nbrR a).card = 1 := by
              intro a ha
              have hpart : (nbrR a ∩ cB).card + (cB \ nbrR a).card = cB.card := by
                have h := Finset.card_sdiff_add_card_inter cB (nbrR a)
                rw [Finset.inter_comm] at h
                exact Nat.add_comm _ _ ▸ h
              have h2 := hdeg_cR a ha
              omega
            have hchoose : ∀ a : Fin n, ∃ x : Fin m, a ∈ cR → cB \ nbrR a = {x} := by
              intro a
              by_cases ha : a ∈ cR
              · rcases Finset.card_eq_one.mp (hmiss_card a ha) with ⟨x, hx⟩
                exact ⟨x, fun _ => hx⟩
              · rcases Finset.card_pos.mp (by omega : 0 < cB.card) with ⟨x0, _⟩
                exact ⟨x0, fun h1 => absurd h1 ha⟩
            choose miss hmiss using hchoose
            have hmiss_mem : ∀ a ∈ cR, miss a ∈ cB := by
              intro a ha
              have hm : miss a ∈ cB \ nbrR a := by rw [hmiss a ha]; simp
              exact (Finset.mem_sdiff.mp hm).1
            have hmiss_inj : Set.InjOn miss (cR : Set (Fin n)) := by
              intro a ha b hb heq
              by_contra hab
              have hsdiff_eq : cB \ nbrR a = cB \ nbrR b := by rw [hmiss a ha, hmiss b hb, heq]
              have hinter_eq : nbrR a ∩ cB = nbrR b ∩ cB := by
                ext x
                have h1 := Finset.ext_iff.mp hsdiff_eq x
                simp only [Finset.mem_inter, Finset.mem_sdiff] at h1 ⊢
                constructor <;> rintro ⟨hx1, hx2⟩ <;> refine ⟨?_, hx2⟩
                · by_contra hnb
                  have := h1.mpr ⟨hx2, hnb⟩
                  exact this.2 hx1
                · by_contra hna
                  have := h1.mp ⟨hx2, hna⟩
                  exact this.2 hx1
              have hsub : nbrR a ∩ cB ⊆ nbrR a ∩ nbrR b := by
                intro x hx
                exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp (hinter_eq ▸ hx)).1⟩
              have hle := Finset.card_le_card hsub
              have h2 := hdeg_cR a ha
              have hi := hc4R a b hab
              omega
            calc cR.card ≤ cB.card := Finset.card_le_card_of_injOn miss hmiss_mem hmiss_inj
              _ = 3 := hcB3
          by_cases hd3 : 3 ≤ d
          · have hR0le : R0.card ≤ d := (Finset.card_le_card hR0_sub_cR).trans (by omega)
            have hB0le : B0.card ≤ d := (Finset.card_le_card hB0_sub_cB).trans (by omega)
            have h1 := hR_le_dt hR0le
            have h2 := hB_le_dt hB0le
            omega
          · have hd2 : d = 2 := by omega
            have hcR3_eq : cR.card = 3 := by omega
            have hR0_eq_cR : R0 = cR := by
              apply Finset.Subset.antisymm hR0_sub_cR
              intro a ha
              refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, ?_⟩
              have hsub : nbrR a ∩ cB ⊆ nbrR a := Finset.inter_subset_left
              have heq : nbrR a ∩ cB = nbrR a :=
                Finset.eq_of_subset_of_card_le hsub (by have := (hnbrR a).2; have := hdeg_cR a ha; omega)
              rw [Finset.eq_empty_iff_forall_notMem]
              intro c hc
              simp only [extR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc
              have hcin : c ∈ nbrR a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2⟩
              rw [← heq] at hcin
              exact hc.1 (Finset.mem_filter.mp (Finset.mem_inter.mp hcin).2).1
            have hdeg_cB : ∀ x ∈ cB, (nbrC x ∩ cR).card = 2 := by
              have hsum_eq : ∑ a ∈ cR, (nbrR a ∩ cB).card = ∑ x ∈ cB, (nbrC x ∩ cR).card := by
                have hL : ∑ a ∈ cR, (nbrR a ∩ cB).card =
                    ∑ a ∈ cR, ∑ x ∈ cB, if G a x = true then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [← Finset.card_filter]
                  congr 1
                  ext x
                  simp only [nbrR, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                  tauto
                have hR : ∑ x ∈ cB, (nbrC x ∩ cR).card =
                    ∑ x ∈ cB, ∑ a ∈ cR, if G a x = true then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [← Finset.card_filter]
                  congr 1
                  ext a
                  simp only [nbrC, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                  tauto
                rw [hL, hR, Finset.sum_comm]
              have hsum6 : ∑ x ∈ cB, (nbrC x ∩ cR).card = 6 := by
                rw [← hsum_eq]
                calc ∑ a ∈ cR, (nbrR a ∩ cB).card = ∑ _a ∈ cR, 2 := Finset.sum_congr rfl hdeg_cR
                  _ = cR.card * 2 := by simp
                  _ = 6 := by omega
              intro x hx
              have hle2 : ∀ y ∈ cB, (nbrC y ∩ cR).card ≤ 2 := fun y _ =>
                (Finset.card_le_card Finset.inter_subset_left).trans (by have := (hnbrC y).2; omega)
              by_contra hne2
              have hlt2 : (nbrC x ∩ cR).card ≤ 1 := by have := hle2 x hx; omega
              have hsum_lt : ∑ y ∈ cB, (nbrC y ∩ cR).card ≤ 5 := by
                rw [← Finset.add_sum_erase _ _ hx]
                have hrest : ∑ y ∈ cB.erase x, (nbrC y ∩ cR).card ≤ (cB.erase x).card * 2 := by
                  calc ∑ y ∈ cB.erase x, (nbrC y ∩ cR).card
                      ≤ ∑ _y ∈ cB.erase x, 2 := Finset.sum_le_sum (fun y hy => hle2 y (Finset.mem_of_mem_erase hy))
                    _ = (cB.erase x).card * 2 := by simp
                have her : (cB.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, hcB3]
                omega
              omega
            have hB0_eq_cB : B0 = cB := by
              apply Finset.Subset.antisymm hB0_sub_cB
              intro x hx
              refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩
              have hsub : nbrC x ∩ cR ⊆ nbrC x := Finset.inter_subset_left
              have heq : nbrC x ∩ cR = nbrC x :=
                Finset.eq_of_subset_of_card_le hsub (by have := (hnbrC x).2; have := hdeg_cB x hx; omega)
              rw [Finset.eq_empty_iff_forall_notMem]
              intro a ha
              simp only [extC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha
              have hain : a ∈ nbrC x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.2⟩
              rw [← heq] at hain
              exact ha.1 (Finset.mem_filter.mp (Finset.mem_inter.mp hain).2).1
            have hR1_le : R1.card ≤ t - 1 := by
              have hinj : Set.InjOn extR (R1 : Set (Fin n)) := by
                intro a ha b hb heq
                by_contra hab
                have han0 : a ∉ cR := by
                  rw [← hR0_eq_cR]
                  intro ha0
                  exact (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha0).2
                have ha_sub : nbrR a ⊆ extR a := by
                  intro c hc
                  have hcB : c ∉ B := by
                    intro hcB
                    exact han0 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, c, hcB, by rw [(Finset.mem_filter.mp hc).2]; decide⟩)
                  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcB⟩, (Finset.mem_filter.mp hc).2⟩
                have hsub : extR a ⊆ nbrR a ∩ nbrR b := by
                  intro c hc
                  have hcb : c ∈ extR b := heq ▸ hc
                  exact Finset.mem_inter.mpr ⟨
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hcb).2⟩⟩
                have hle := (Finset.card_le_card ha_sub).trans ((Finset.card_le_card hsub).trans (hc4R a b hab))
                have h2 := (hnbrR a).1
                omega
              have hmem0 : (∅ : Finset (Fin m)) ∈ R.image extR := by
                rcases Finset.card_pos.mp (by rw [hR0_eq_cR]; omega : 0 < R0.card) with ⟨a, ha⟩
                exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
              have hsub : R1.image extR ⊆ (R.image extR).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ha).2,
                  Finset.mem_image_of_mem extR (Finset.mem_filter.mp ha).1⟩
              rw [← Finset.card_image_of_injOn hinj]
              have hle := Finset.card_le_card hsub
              rw [Finset.card_erase_of_mem hmem0] at hle
              omega
            have hB1_le : B1.card ≤ t - 1 := by
              have hinj : Set.InjOn extC (B1 : Set (Fin m)) := by
                intro x hx y hy heq
                by_contra hxy
                have hxn0 : x ∉ cB := by
                  rw [← hB0_eq_cB]
                  intro hx0
                  exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx0).2
                have hx_sub : nbrC x ⊆ extC x := by
                  intro a ha
                  have haR : a ∉ R := by
                    intro haR
                    exact hxn0 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, a, haR, by rw [(Finset.mem_filter.mp ha).2]; decide⟩)
                  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haR⟩, (Finset.mem_filter.mp ha).2⟩
                have hsub : extC x ⊆ nbrC x ∩ nbrC y := by
                  intro a ha
                  have hay : a ∈ extC y := heq ▸ ha
                  exact Finset.mem_inter.mpr ⟨
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hay).2⟩⟩
                have hle := (Finset.card_le_card hx_sub).trans ((Finset.card_le_card hsub).trans (hc4C x y hxy))
                have h2 := (hnbrC x).1
                omega
              have hmem0 : (∅ : Finset (Fin n)) ∈ B.image extC := by
                rcases Finset.card_pos.mp (by rw [hB0_eq_cB]; omega : 0 < B0.card) with ⟨x, hx⟩
                exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
              have hsub : B1.image extC ⊆ (B.image extC).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨x, hx, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hx).2,
                  Finset.mem_image_of_mem extC (Finset.mem_filter.mp hx).1⟩
              rw [← Finset.card_image_of_injOn hinj]
              have hle := Finset.card_le_card hsub
              rw [Finset.card_erase_of_mem hmem0] at hle
              omega
            rw [hR0_eq_cR, hcR3_eq] at hRsum
            rw [hB0_eq_cB, hcB3] at hBsum
            have h4t : 2 * d * t = 4 * t := by rw [hd2]
            omega
  · by_cases hfullR : ∃ a0 ∈ R, ∀ x ∈ B, G a0 x = true
    · rcases hfullR with ⟨a0, _, ha0⟩
      have hB_le_d : B.card ≤ d := by
        have hsub : B ⊆ nbrR a0 := fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0 x hx⟩
        exact (Finset.card_le_card hsub).trans (hnbrR a0).2
      have hR0_le1 : R0.card ≤ 1 := by
        have hsub : R0 ⊆ {a0} := by
          intro a ha
          simp only [Finset.mem_singleton]
          by_contra ha0ne
          have hsub2 : nbrR a ⊆ nbrR a ∩ nbrR a0 := by
            intro x hx
            exact Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0 x (hR0_sub_B a ha hx)⟩⟩
          have hle := (Finset.card_le_card hsub2).trans (hc4R a a0 ha0ne)
          have h2 := (hnbrR a).1
          omega
        exact (Finset.card_le_card hsub).trans (by simp)
      have hRle := hR_le_dt (by omega)
      have hdt_ge : d ≤ d * t := by
        calc d = d * 1 := (Nat.mul_one d).symm
          _ ≤ d * t := Nat.mul_le_mul_left d (by omega)
      omega
    · by_cases hfullB : ∃ c0 ∈ B, ∀ a ∈ R, G a c0 = true
      · rcases hfullB with ⟨c0, _, hc0⟩
        have hR_le_d : R.card ≤ d := by
          have hsub : R ⊆ nbrC c0 := fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0 a ha⟩
          exact (Finset.card_le_card hsub).trans (hnbrC c0).2
        have hB0_le1 : B0.card ≤ 1 := by
          have hsub : B0 ⊆ {c0} := by
            intro c hc
            simp only [Finset.mem_singleton]
            by_contra hc0ne
            have hsub2 : nbrC c ⊆ nbrC c ∩ nbrC c0 := by
              intro a ha
              exact Finset.mem_inter.mpr ⟨ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0 a (hB0_sub_R c hc ha)⟩⟩
            have hle := (Finset.card_le_card hsub2).trans (hc4C c c0 hc0ne)
            have h2 := (hnbrC c).1
            omega
          exact (Finset.card_le_card hsub).trans (by simp)
        have hBle := hB_le_dt (by omega)
        have hdt_ge : d ≤ d * t := by
          calc d = d * 1 := (Nat.mul_one d).symm
            _ ≤ d * t := Nat.mul_le_mul_left d (by omega)
        omega
      · have hrect_all : ∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
            G a x = true → G b x = true → G b y = true → G a y = true := by
          intro a ha b hb x hx y hy hax hbx hby
          have hcoreR : ∀ r ∈ R, r ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ true) := by
            intro r hr
            refine Finset.mem_filter.mpr ⟨hr, ?_⟩
            by_contra hno
            apply hfullR
            refine ⟨r, hr, fun w hw => ?_⟩
            cases hG : G r w
            · exact absurd ⟨w, hw, by rw [hG]; decide⟩ hno
            · rfl
          have hcoreC : ∀ c ∈ B, c ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ true) := by
            intro c hc
            refine Finset.mem_filter.mpr ⟨hc, ?_⟩
            by_contra hno
            apply hfullB
            refine ⟨c, hc, fun w hw => ?_⟩
            cases hG : G w c
            · exact absurd ⟨w, hw, by rw [hG]; decide⟩ hno
            · rfl
          exact hrect a (hcoreR a ha) b (hcoreR b hb) x (hcoreC x hx) y (hcoreC y hy) hax hbx hby
        by_cases hR0ne : R0.Nonempty
        · by_cases hB0ne : B0.Nonempty
          · have hR1_le_L : R1.card ≤ L := by
              have hmem0 : (∅ : Finset (Fin m)) ∈ R.image extR := by
                rcases hR0ne with ⟨a, ha⟩
                exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
              have hsub : R1.image extR ⊆ (R.image extR).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ha).2,
                  Finset.mem_image_of_mem extR (Finset.mem_filter.mp ha).1⟩
              have him1 : (R1.image extR).card ≤ t - 1 := by
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_erase_of_mem hmem0] at h1
                omega
              have hle := card_le_mul_of_fiber_bound R1 extR (t - 1) d him1 (by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
                have hPne : (extR a).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp ha).2
                calc (R1.filter (fun r => extR r = extR a)).card
                    ≤ (R.filter (fun r => extR r = extR a)).card := by
                      apply Finset.card_le_card
                      intro r hr
                      simp only [R1, Finset.mem_filter] at hr ⊢
                      exact ⟨hr.1.1, hr.2⟩
                  _ ≤ d := hfibR (extR a) hPne)
              rw [Nat.mul_comm] at hle
              exact hle
            have hB1_le_L : B1.card ≤ L := by
              have hmem0 : (∅ : Finset (Fin n)) ∈ B.image extC := by
                rcases hB0ne with ⟨c, hc⟩
                exact Finset.mem_image.mpr ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2⟩
              have hsub : B1.image extC ⊆ (B.image extC).erase ∅ := by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hc).2,
                  Finset.mem_image_of_mem extC (Finset.mem_filter.mp hc).1⟩
              have him1 : (B1.image extC).card ≤ t - 1 := by
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_erase_of_mem hmem0] at h1
                omega
              have hle := card_le_mul_of_fiber_bound B1 extC (t - 1) d him1 (by
                intro P hP
                rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
                have hPne : (extC c).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hc).2
                calc (B1.filter (fun x => extC x = extC c)).card
                    ≤ (B.filter (fun x => extC x = extC c)).card := by
                      apply Finset.card_le_card
                      intro x hx
                      simp only [B1, Finset.mem_filter] at hx ⊢
                      exact ⟨hx.1.1, hx.2⟩
                  _ ≤ d := hfibB (extC c) hPne)
              rw [Nat.mul_comm] at hle
              exact hle
            have hstar_R0 : ∀ a ∈ R0, ∀ x ∈ nbrR a, ∀ b ∈ R, G b x = true → b = a := by
              intro a ha x hx b hb hbx
              have haR : a ∈ R := (Finset.mem_filter.mp ha).1
              have hxB : x ∈ B := hR0_sub_B a ha hx
              by_contra hba
              have hne : ((nbrR a).erase x).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hem
                have h1 := Finset.card_erase_of_mem hx
                rw [hem] at h1; simp at h1
                have h2 := (hnbrR a).1
                omega
              rcases hne with ⟨y, hy⟩
              rcases Finset.mem_erase.mp hy with ⟨hyx, hyN⟩
              have hyB : y ∈ B := hR0_sub_B a ha hyN
              have hax : G a x = true := (Finset.mem_filter.mp hx).2
              have hay : G a y = true := (Finset.mem_filter.mp hyN).2
              have hby : G b y = true := hrect_all b hb a haR x hxB y hyB hbx hax hay
              have hsub : ({x, y} : Finset (Fin m)) ⊆ nbrR a ∩ nbrR b := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                simp only [nbrR, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases hc with rfl | rfl
                · exact ⟨hax, hbx⟩
                · exact ⟨hay, hby⟩
              have hpair : ({x, y} : Finset (Fin m)).card = 2 := Finset.card_pair (Ne.symm hyx)
              have hle := Finset.card_le_card hsub
              have h1 := hc4R a b (Ne.symm hba)
              omega
            have hstar_B0 : ∀ x ∈ B0, ∀ a ∈ nbrC x, ∀ y ∈ B, G a y = true → y = x := by
              intro x hx a ha y hy hay
              have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
              have haR : a ∈ R := hB0_sub_R x hx ha
              by_contra hyx
              have hne : ((nbrC x).erase a).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hem
                have h1 := Finset.card_erase_of_mem ha
                rw [hem] at h1; simp at h1
                have h2 := (hnbrC x).1
                omega
              rcases hne with ⟨b, hb⟩
              rcases Finset.mem_erase.mp hb with ⟨hba, hbN⟩
              have hbR : b ∈ R := hB0_sub_R x hx hbN
              have hax : G a x = true := (Finset.mem_filter.mp ha).2
              have hbx : G b x = true := (Finset.mem_filter.mp hbN).2
              have hby : G b y = true := hrect_all b hbR a haR x hxB y hy hbx hax hay
              have hsub : ({a, b} : Finset (Fin n)) ⊆ nbrC x ∩ nbrC y := by
                intro r hr
                simp only [Finset.mem_insert, Finset.mem_singleton] at hr
                simp only [nbrC, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases hr with rfl | rfl
                · exact ⟨hax, hay⟩
                · exact ⟨hbx, hby⟩
              have hpair : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair (Ne.symm hba)
              have hle := Finset.card_le_card hsub
              have h1 := hc4C x y (Ne.symm hyx)
              omega
            have h2R0_le_B1 : 2 * R0.card ≤ B1.card := by
              have hsub : R0.biUnion nbrR ⊆ B1 := by
                intro x hx
                rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hax⟩
                have hxB : x ∈ B := hR0_sub_B a ha hax
                refine Finset.mem_filter.mpr ⟨hxB, ?_⟩
                intro hx0
                have hne : ((nbrC x).erase a).Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hem
                  have haN : a ∈ nbrC x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hax).2⟩
                  have h1 := Finset.card_erase_of_mem haN
                  rw [hem] at h1; simp at h1
                  have h2 := (hnbrC x).1
                  omega
                rcases hne with ⟨b, hb⟩
                rcases Finset.mem_erase.mp hb with ⟨hba, hbN⟩
                have hbR : b ∈ R := hB0_sub_R x (Finset.mem_filter.mpr ⟨hxB, hx0⟩) hbN
                exact hba (hstar_R0 a ha x hax b hbR (Finset.mem_filter.mp hbN).2)
              have hdisj : Set.PairwiseDisjoint (R0 : Set (Fin n)) nbrR := by
                intro a ha b hb hab
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro x hax hbx
                exact hab (hstar_R0 a ha x hax b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hbx).2).symm
              calc 2 * R0.card = ∑ _a ∈ R0, 2 := by simp [Nat.mul_comm]
                _ ≤ ∑ a ∈ R0, (nbrR a).card := Finset.sum_le_sum (fun a _ => (hnbrR a).1)
                _ = (R0.biUnion nbrR).card := (Finset.card_biUnion hdisj).symm
                _ ≤ B1.card := Finset.card_le_card hsub
            have h2B0_le_R1 : 2 * B0.card ≤ R1.card := by
              have hsub : B0.biUnion nbrC ⊆ R1 := by
                intro a ha
                rcases Finset.mem_biUnion.mp ha with ⟨x, hx, hax⟩
                have haR : a ∈ R := hB0_sub_R x hx hax
                refine Finset.mem_filter.mpr ⟨haR, ?_⟩
                intro ha0
                have hne : ((nbrR a).erase x).Nonempty := by
                  rw [Finset.nonempty_iff_ne_empty]
                  intro hem
                  have hxN : x ∈ nbrR a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hax).2⟩
                  have h1 := Finset.card_erase_of_mem hxN
                  rw [hem] at h1; simp at h1
                  have h2 := (hnbrR a).1
                  omega
                rcases hne with ⟨y, hy⟩
                rcases Finset.mem_erase.mp hy with ⟨hyx, hyN⟩
                have hyB : y ∈ B := hR0_sub_B a (Finset.mem_filter.mpr ⟨haR, ha0⟩) hyN
                exact hyx (hstar_B0 x hx a hax y hyB (Finset.mem_filter.mp hyN).2)
              have hdisj : Set.PairwiseDisjoint (B0 : Set (Fin m)) nbrC := by
                intro x hx y hy hxy
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro a hax hay
                exact hxy (hstar_B0 x hx a hax y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hay).2).symm
              calc 2 * B0.card = ∑ _x ∈ B0, 2 := by simp [Nat.mul_comm]
                _ ≤ ∑ x ∈ B0, (nbrC x).card := Finset.sum_le_sum (fun x _ => (hnbrC x).1)
                _ = (B0.biUnion nbrC).card := (Finset.card_biUnion hdisj).symm
                _ ≤ R1.card := Finset.card_le_card hsub
            omega
          · have hB0em : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB0ne
            have hT := upper_bound_one_empty_side d t m n (fun c a => G a c) B R hd ht
              hnbrC hnbrR hc4C hcolT hrowT
              (fun x hx y hy a ha b hb hxa hya hyb => hrect_all b hb a ha y hy x hx hyb hya hxa)
              hB0em hR0ne
            omega
        · by_cases hB0ne : B0.Nonempty
          · have hR0em : R0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR0ne
            exact upper_bound_one_empty_side d t n m G R B hd ht
              hnbrR hnbrC hc4R hrowT hcolT hrect_all hR0em hB0ne
          · have hR0em : R0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR0ne
            have hB0em : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB0ne
            have h1 := hR_le_dt (by rw [hR0em]; simp)
            have h2 := hB_le_dt (by rw [hB0em]; simp)
            omega

private theorem exists_matching_true (d t : Nat) (hd : 2 ≤ d) (ht : 2 ≤ t) :
    ∃ (n m : Nat) (G : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)),
      admissible d t n m G true R B ∧ R.card + B.card = 2 * d * t := by
  let N := d * t
  let n := N + t
  let G : Fin n → Fin n → Bool := fun a c =>
    (a.val < N ∧ c.val < N ∧ a.val = c.val) ||
    (a.val < N ∧ N ≤ c.val ∧ c.val - N = a.val / d) ||
    (N ≤ a.val ∧ c.val < N ∧ a.val - N = c.val / d)
  let R : Finset (Fin n) := Finset.univ.filter (fun a => a.val < N)
  let B : Finset (Fin n) := Finset.univ.filter (fun c => c.val < N)
  have hG_iff : ∀ a c : Fin n, G a c = true ↔
      (a.val < N ∧ c.val < N ∧ a.val = c.val) ∨
      (a.val < N ∧ N ≤ c.val ∧ c.val - N = a.val / d) ∨
      (N ≤ a.val ∧ c.val < N ∧ a.val - N = c.val / d) := by
    intro a c
    simp only [G, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
  have hG_symm : ∀ a c : Fin n, G a c = G c a := by
    intro a c
    apply Bool.eq_iff_iff.mpr
    rw [hG_iff, hG_iff]
    constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
    · exact Or.inr (Or.inl ⟨h2, h1, h3⟩)
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
    · exact Or.inr (Or.inl ⟨h2, h1, h3⟩)
  have hR_card : R.card = N := by
    have hinj : Function.Injective (fun i : Fin N => (⟨i.val, by omega⟩ : Fin n)) := by
      intro i j h; exact Fin.ext (by simpa using congrArg Fin.val h)
    have him : R = Finset.univ.image (fun i : Fin N => (⟨i.val, by omega⟩ : Fin n)) := by
      ext a
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ha; exact ⟨⟨a.val, ha⟩, rfl⟩
      · rintro ⟨i, rfl⟩; exact i.isLt
    rw [him, Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hdegR : ∀ a : Fin n,
      2 ≤ (Finset.univ.filter (fun c : Fin n => G a c = true)).card ∧
      (Finset.univ.filter (fun c : Fin n => G a c = true)).card ≤ d := by
    intro a
    by_cases ha : a.val < N
    · have hdiv_lt : a.val / d < t := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d)]
        rw [Nat.mul_comm]
        exact ha
      let c1 : Fin n := ⟨a.val, by omega⟩
      let c2 : Fin n := ⟨N + a.val / d, by omega⟩
      have hne : c1 ≠ c2 := fun h => by
        have hv : a.val = N + a.val / d := congrArg Fin.val h
        have hle := Nat.le_add_right N (a.val / d)
        omega
      have hset : Finset.univ.filter (fun c : Fin n => G a c = true) = {c1, c2} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hG_iff]
        constructor
        · rintro (⟨_, _, h3⟩ | ⟨_, h2, h3⟩ | ⟨h1, _, _⟩)
          · left; exact Fin.ext h3.symm
          · right; exact Fin.ext (by simp only [c2]; omega)
          · omega
        · rintro (rfl | rfl)
          · exact Or.inl ⟨ha, ha, rfl⟩
          · exact Or.inr (Or.inl ⟨ha, Nat.le_add_right N (a.val / d), Nat.add_sub_cancel_left N (a.val / d)⟩)
      rw [hset, Finset.card_pair hne]
      exact ⟨le_refl 2, hd⟩
    · have ha_ge : N ≤ a.val := by omega
      let q := a.val - N
      have hq : q < t := by omega
      have hmul : (q + 1) * d ≤ N := by
        calc (q + 1) * d ≤ t * d := Nat.mul_le_mul_right d hq
          _ = d * t := Nat.mul_comm t d
      have hqd : q * d + d = (q + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      have hinj : Function.Injective (fun r : Fin d => (⟨q * d + r.val, by omega⟩ : Fin n)) := by
        intro r1 r2 h; exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
      have hset : Finset.univ.filter (fun c : Fin n => G a c = true) =
          Finset.univ.image (fun r : Fin d => (⟨q * d + r.val, by omega⟩ : Fin n)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hG_iff]
        constructor
        · rintro (⟨h1, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, h3⟩)
          · omega
          · omega
          · refine ⟨⟨c.val % d, Nat.mod_lt _ (by omega)⟩, Fin.ext ?_⟩
            dsimp
            have hdm := Nat.div_add_mod c.val d
            have hqeq : q = c.val / d := h3
            rw [hqeq, Nat.mul_comm]
            exact hdm
        · rintro ⟨r, rfl⟩
          refine Or.inr (Or.inr ⟨ha_ge, by dsimp only; omega, ?_⟩)
          dsimp
          have hdiv : (q * d + r.val) / d = q := by
            rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < d), Nat.div_eq_of_lt r.isLt, Nat.add_zero]
          exact hdiv.symm
      rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_fin]
      exact ⟨hd, le_refl d⟩
  have hdegC : ∀ c : Fin n,
      2 ≤ (Finset.univ.filter (fun a : Fin n => G a c = true)).card ∧
      (Finset.univ.filter (fun a : Fin n => G a c = true)).card ≤ d := by
    intro c
    have heq : Finset.univ.filter (fun a : Fin n => G a c = true) =
        Finset.univ.filter (fun a : Fin n => G c a = true) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hG_symm]
    rw [heq]
    exact hdegR c
  have hc4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (fun c : Fin n => G a c = true)) ∩
       (Finset.univ.filter (fun c : Fin n => G b c = true))).card ≤ 1 := by
    intro a b hab
    rw [Finset.card_le_one]
    intro c₁ hc₁ c₂ hc₂
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hG_iff] at hc₁ hc₂
    rcases hc₁ with ⟨ha1, hb1⟩
    rcases hc₂ with ⟨ha2, hb2⟩
    rcases ha1 with ⟨haN, hc1N, ha1eq⟩ | ⟨haN, hc1ge, ha1div⟩ | ⟨hage, hc1N, ha1div⟩
    · rcases ha2 with ⟨_, hc2N, ha2eq⟩ | ⟨_, hc2ge, ha2div⟩ | ⟨hage, _, _⟩
      · exact Fin.ext (ha1eq.symm.trans ha2eq)
      · rcases hb1 with ⟨hbN, _, hb1eq⟩ | ⟨_, hb1ge, _⟩ | ⟨hbge, _, _⟩
        · exact absurd (Fin.ext (ha1eq.trans hb1eq.symm)) hab
        · omega
        · rcases hb2 with ⟨hbN, _, _⟩ | ⟨hbN, _, _⟩ | ⟨_, hc2N, _⟩ <;> omega
      · omega
    · rcases ha2 with ⟨_, hc2N, ha2eq⟩ | ⟨_, hc2ge, ha2div⟩ | ⟨hage, _, _⟩
      · rcases hb2 with ⟨hbN, _, hb2eq⟩ | ⟨_, hb2ge, _⟩ | ⟨hbge, _, _⟩
        · exact absurd (Fin.ext (ha2eq.trans hb2eq.symm)) hab
        · omega
        · rcases hb1 with ⟨hbN, _, _⟩ | ⟨hbN, _, _⟩ | ⟨_, hc1N, _⟩ <;> omega
      · exact Fin.ext (by omega)
      · omega
    · rcases hb1 with ⟨hbN, _, hb1eq⟩ | ⟨_, hb1ge, _⟩ | ⟨hbge, _, hb1div⟩
      · rcases hb2 with ⟨_, _, hb2eq⟩ | ⟨_, hc2ge, _⟩ | ⟨hbge, _, _⟩
        · exact Fin.ext (hb1eq.symm.trans hb2eq)
        · rcases ha2 with ⟨haN, _, _⟩ | ⟨haN, _, _⟩ | ⟨_, hc2N, _⟩ <;> omega
        · omega
      · omega
      · exact absurd (Fin.ext (by omega)) hab
  have hrowT : (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤ t := by
    let φ : Fin t → Finset (Fin n) := fun p => {⟨N + p.val, by omega⟩}
    have hsub : R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true)) ⊆
        Finset.univ.image φ := by
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨a, ha, rfl⟩
      have haN : a.val < N := (Finset.mem_filter.mp ha).2
      have hdiv_lt : a.val / d < t := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d), Nat.mul_comm]
        exact haN
      refine Finset.mem_image.mpr ⟨⟨a.val / d, hdiv_lt⟩, Finset.mem_univ _, ?_⟩
      ext c
      simp only [φ, B, Finset.mem_singleton, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and, not_lt, hG_iff]
      constructor
      · rintro rfl
        exact ⟨Nat.le_add_right N (a.val / d), Or.inr (Or.inl ⟨haN, Nat.le_add_right N (a.val / d), Nat.add_sub_cancel_left N (a.val / d)⟩)⟩
      · rintro ⟨hcge, (⟨_, hcN, _⟩ | ⟨_, _, hdiv⟩ | ⟨hage, _, _⟩)⟩
        · omega
        · exact Fin.ext (by dsimp; omega)
        · omega
    calc (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card
        ≤ (Finset.univ.image φ).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
      _ = t := Finset.card_fin t
  have hcolT : (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤ t := by
    have heq : B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true)) =
        R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true)) := by
      ext S
      simp only [Finset.mem_image]
      constructor <;> rintro ⟨x, hx, rfl⟩ <;> refine ⟨x, hx, ?_⟩ <;> ext y <;>
        (simp only [R, B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]; rw [hG_symm])
    rw [heq]
    exact hrowT
  refine ⟨n, n, G, R, B, ⟨hdegR, hdegC, hc4, hrowT, hcolT, true, ?_⟩, ?_⟩
  · intro a ha b hb x hx y hy hax hbx hby
    have haR : a.val < N := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have hbR : b.val < N := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    have hxB : x.val < N := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hyB : y.val < N := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    rw [hG_iff] at hax hbx hby ⊢
    rcases hax with ⟨_, _, h1⟩ | ⟨_, h2, _⟩ | ⟨h1, _, _⟩
    · rcases hbx with ⟨_, _, h2⟩ | ⟨_, h2, _⟩ | ⟨h2, _, _⟩
      · rcases hby with ⟨_, _, h3⟩ | ⟨_, h3, _⟩ | ⟨h3, _, _⟩
        · exact Or.inl ⟨haR, hyB, by omega⟩
        · omega
        · omega
      · omega
      · omega
    · omega
    · omega
  · rw [hR_card]
    change N + N = 2 * d * t
    dsimp [N]
    rw [Nat.two_mul, Nat.add_mul]

private theorem exists_stars_true (d t : Nat) (hd : 2 ≤ d) (ht4 : 4 ≤ t) :
    ∃ (n m : Nat) (G : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)),
      admissible d t n m G true R B ∧
      R.card + B.card = 2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2) := by
  let L := d * (t - 1)
  let k := L / 2
  have htm1 : 3 ≤ t - 1 := by omega
  have hL6 : 6 ≤ L := by
    calc 6 = 2 * 3 := by rfl
      _ ≤ d * (t - 1) := Nat.mul_le_mul hd htm1
  have hk3 : 3 ≤ k := by omega
  have hL_le_2k1 : L ≤ 2 * k + 1 := by omega
  let n := L + k + (t - 1)
  let grp : Nat → Nat := fun i => min (i / 2) (k - 1)
  have hgrp_lt : ∀ i, grp i < k := by
    intro i; dsimp [grp]; omega
  have hgrp_close : ∀ i j, i < L → j < L → grp i = grp j → i ≤ j + 2 ∧ j ≤ i + 2 := by
    intro i j hi hj heq
    dsimp [grp] at heq
    omega
  have hgrp_mod_inj : ∀ i j, i < L → j < L → grp i = grp j → i % (t - 1) = j % (t - 1) → i = j := by
    intro i j hi hj hgeq hmeq
    have hcl := hgrp_close i j hi hj hgeq
    by_contra hne
    have h1 : ∀ a b : Nat, a < b → b ≤ a + 2 → a % (t - 1) = b % (t - 1) → False := by
      intro a b hab hle hm
      have hdiff : 1 ≤ b - a ∧ b - a ≤ 2 := by omega
      have hb_eq : b = a + (b - a) := by omega
      have hmod : (a + (b - a)) % (t - 1) = (a % (t - 1) + (b - a) % (t - 1)) % (t - 1) := Nat.add_mod _ _ _
      rw [← hb_eq, ← hm] at hmod
      have hlt : b - a < t - 1 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hmod
      have ham : a % (t - 1) < t - 1 := Nat.mod_lt a (by omega)
      by_cases hsum : a % (t - 1) + (b - a) < t - 1
      · rw [Nat.mod_eq_of_lt hsum] at hmod; omega
      · have hmod2 : (a % (t - 1) + (b - a)) % (t - 1) = a % (t - 1) + (b - a) - (t - 1) := by
          rw [Nat.mod_eq_sub_mod (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod2] at hmod
        omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact h1 i j hlt hcl.2 hmeq
    · exact h1 j i hgt hcl.1 hmeq.symm
  let G : Fin n → Fin n → Bool := fun a c =>
    (a.val < L ∧ L ≤ c.val ∧ c.val < L + k ∧ c.val - L = grp a.val) ||
    (a.val < L ∧ L + k ≤ c.val ∧ c.val - (L + k) = a.val % (t - 1)) ||
    (L ≤ a.val ∧ a.val < L + k ∧ c.val < L ∧ a.val - L = grp c.val) ||
    (L + k ≤ a.val ∧ c.val < L ∧ a.val - (L + k) = c.val % (t - 1))
  let R : Finset (Fin n) := Finset.univ.filter (fun a => a.val < L + k)
  let B : Finset (Fin n) := Finset.univ.filter (fun c => c.val < L + k)
  have hG_iff : ∀ a c : Fin n, G a c = true ↔
      (a.val < L ∧ L ≤ c.val ∧ c.val < L + k ∧ c.val - L = grp a.val) ∨
      (a.val < L ∧ L + k ≤ c.val ∧ c.val - (L + k) = a.val % (t - 1)) ∨
      (L ≤ a.val ∧ a.val < L + k ∧ c.val < L ∧ a.val - L = grp c.val) ∨
      (L + k ≤ a.val ∧ c.val < L ∧ a.val - (L + k) = c.val % (t - 1)) := by
    intro a c
    simp only [G, Bool.or_eq_true, decide_eq_true_eq, or_assoc]
  have hG_symm : ∀ a c : Fin n, G a c = G c a := by
    intro a c
    apply Bool.eq_iff_iff.mpr
    rw [hG_iff, hG_iff]
    constructor <;> rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2.1, h.1, h.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩))
    · exact Or.inl ⟨h.2.2.1, h.1, h.2.1, h.2.2.2⟩
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2.1, h.1, h.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩))
    · exact Or.inl ⟨h.2.2.1, h.1, h.2.1, h.2.2.2⟩
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)
  have hR_card : R.card = L + k := by
    have hinj : Function.Injective (fun i : Fin (L + k) => (⟨i.val, by omega⟩ : Fin n)) := by
      intro i j h; exact Fin.ext (by simpa using congrArg Fin.val h)
    have him : R = Finset.univ.image (fun i : Fin (L + k) => (⟨i.val, by omega⟩ : Fin n)) := by
      ext a
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro ha; exact ⟨⟨a.val, ha⟩, rfl⟩
      · rintro ⟨i, rfl⟩; exact i.isLt
    rw [him, Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hdegR : ∀ a : Fin n,
      2 ≤ (Finset.univ.filter (fun c : Fin n => G a c = true)).card ∧
      (Finset.univ.filter (fun c : Fin n => G a c = true)).card ≤ d := by
    intro a
    by_cases haL : a.val < L
    · let c1 : Fin n := ⟨L + grp a.val, by have := hgrp_lt a.val; omega⟩
      let c2 : Fin n := ⟨L + k + a.val % (t - 1), by have := Nat.mod_lt a.val (by omega : 0 < t - 1); omega⟩
      have hne : c1 ≠ c2 := fun h => by
        have := congrArg Fin.val h; dsimp [c1, c2] at this; have := hgrp_lt a.val; omega
      have hset : Finset.univ.filter (fun c : Fin n => G a c = true) = {c1, c2} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hG_iff]
        constructor
        · rintro (⟨_, h1, h2, h3⟩ | ⟨_, h1, h2⟩ | ⟨h1, _, _, _⟩ | ⟨h1, _, _⟩)
          · left; exact Fin.ext (by dsimp [c1]; omega)
          · right; exact Fin.ext (by dsimp [c2]; omega)
          · omega
          · omega
        · rintro (rfl | rfl)
          · exact Or.inl ⟨haL, by dsimp [c1]; omega, by dsimp [c1]; have := hgrp_lt a.val; omega, by dsimp [c1]; omega⟩
          · exact Or.inr (Or.inl ⟨haL, by dsimp [c2]; omega, by dsimp [c2]; omega⟩)
      rw [hset, Finset.card_pair hne]
      exact ⟨le_refl 2, hd⟩
    · by_cases haLk : a.val < L + k
      · let j := a.val - L
        have hj : j < k := by omega
        by_cases hjlast : j = k - 1 ∧ L = 2 * k + 1
        · rcases hjlast with ⟨hjeq, hLodd⟩
          have hd3 : 3 ≤ d := by
            by_contra hlt3
            have hd2 : d = 2 := by omega
            have hLeven : L = 2 * (t - 1) := by dsimp [L]; rw [hd2]
            omega
          let c1 : Fin n := ⟨2 * j, by omega⟩
          let c2 : Fin n := ⟨2 * j + 1, by omega⟩
          let c3 : Fin n := ⟨2 * j + 2, by omega⟩
          have h12 : c1 ≠ c2 := fun h => by have := congrArg Fin.val h; dsimp [c1, c2] at this; omega
          have h13 : c1 ≠ c3 := fun h => by have := congrArg Fin.val h; dsimp [c1, c3] at this; omega
          have h23 : c2 ≠ c3 := fun h => by have := congrArg Fin.val h; dsimp [c2, c3] at this; omega
          have hset : Finset.univ.filter (fun c : Fin n => G a c = true) = {c1, c2, c3} := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hG_iff]
            constructor
            · rintro (⟨h1, _, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, hcL, hgeq⟩ | ⟨h1, _, _⟩)
              · omega
              · omega
              · dsimp [grp] at hgeq
                have hc_cases : c.val = 2 * j ∨ c.val = 2 * j + 1 ∨ c.val = 2 * j + 2 := by omega
                rcases hc_cases with h | h | h
                · left; exact Fin.ext h
                · right; left; exact Fin.ext h
                · right; right; exact Fin.ext h
              · omega
            · rintro (rfl | rfl | rfl)
              · exact Or.inr (Or.inr (Or.inl ⟨by omega, haLk, by dsimp [c1]; omega, by dsimp [c1, grp, j]; omega⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨by omega, haLk, by dsimp [c2]; omega, by dsimp [c2, grp, j]; omega⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨by omega, haLk, by dsimp [c3]; omega, by dsimp [c3, grp, j]; omega⟩))
          rw [hset, Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
          exact ⟨by omega, hd3⟩
        · let c1 : Fin n := ⟨2 * j, by omega⟩
          let c2 : Fin n := ⟨2 * j + 1, by omega⟩
          have h12 : c1 ≠ c2 := fun h => by have := congrArg Fin.val h; dsimp [c1, c2] at this; omega
          have hset : Finset.univ.filter (fun c : Fin n => G a c = true) = {c1, c2} := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hG_iff]
            constructor
            · rintro (⟨h1, _, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, hcL, hgeq⟩ | ⟨h1, _, _⟩)
              · omega
              · omega
              · dsimp [grp] at hgeq
                have hc_cases : c.val = 2 * j ∨ c.val = 2 * j + 1 := by omega
                rcases hc_cases with h | h
                · left; exact Fin.ext h
                · right; exact Fin.ext h
              · omega
            · rintro (rfl | rfl)
              · exact Or.inr (Or.inr (Or.inl ⟨by omega, haLk, by dsimp [c1]; omega, by dsimp [c1, grp, j]; omega⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨by omega, haLk, by dsimp [c2]; omega, by dsimp [c2, grp, j]; omega⟩))
          rw [hset, Finset.card_pair h12]
          exact ⟨le_refl 2, hd⟩
      · let p := a.val - (L + k)
        have hp : p < t - 1 := by omega
        have hinj : Function.Injective (fun q : Fin d => (⟨q.val * (t - 1) + p, by
            have h1 : (q.val + 1) * (t - 1) ≤ d * (t - 1) := Nat.mul_le_mul_right (t - 1) q.isLt
            have h2 : q.val * (t - 1) + (t - 1) = (q.val + 1) * (t - 1) := by rw [Nat.add_mul, Nat.one_mul]
            omega⟩ : Fin n)) := by
          intro q1 q2 h
          have hv := congrArg Fin.val h; dsimp at hv
          have hmul : q1.val * (t - 1) = q2.val * (t - 1) := by omega
          exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < t - 1) hmul)
        have hset : Finset.univ.filter (fun c : Fin n => G a c = true) =
            Finset.univ.image (fun q : Fin d => (⟨q.val * (t - 1) + p, by
              have h1 : (q.val + 1) * (t - 1) ≤ d * (t - 1) := Nat.mul_le_mul_right (t - 1) q.isLt
              have h2 : q.val * (t - 1) + (t - 1) = (q.val + 1) * (t - 1) := by rw [Nat.add_mul, Nat.one_mul]
              omega⟩ : Fin n)) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hG_iff]
          constructor
          · rintro (⟨h1, _, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, h2, _, _⟩ | ⟨_, hcL, hmod⟩)
            · omega
            · omega
            · omega
            · have hqlt : c.val / (t - 1) < d := by
                rw [Nat.div_lt_iff_lt_mul (by omega : 0 < t - 1)]
                exact hcL
              refine ⟨⟨c.val / (t - 1), hqlt⟩, Fin.ext ?_⟩
              dsimp
              have hdm := Nat.div_add_mod c.val (t - 1)
              have hpeq : p = c.val % (t - 1) := hmod
              rw [hpeq, Nat.mul_comm]
              exact hdm
          · rintro ⟨q, rfl⟩
            have h1 : (q.val + 1) * (t - 1) ≤ d * (t - 1) := Nat.mul_le_mul_right (t - 1) q.isLt
            have h2 : q.val * (t - 1) + (t - 1) = (q.val + 1) * (t - 1) := by rw [Nat.add_mul, Nat.one_mul]
            refine Or.inr (Or.inr (Or.inr ⟨by omega, by dsimp; omega, ?_⟩))
            dsimp
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
        rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_fin]
        exact ⟨hd, le_refl d⟩
  have hdegC : ∀ c : Fin n,
      2 ≤ (Finset.univ.filter (fun a : Fin n => G a c = true)).card ∧
      (Finset.univ.filter (fun a : Fin n => G a c = true)).card ≤ d := by
    intro c
    have heq : Finset.univ.filter (fun a : Fin n => G a c = true) =
        Finset.univ.filter (fun a : Fin n => G c a = true) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hG_symm]
    rw [heq]
    exact hdegR c
  have hc4 : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (fun c : Fin n => G a c = true)) ∩
       (Finset.univ.filter (fun c : Fin n => G b c = true))).card ≤ 1 := by
    intro a b hab
    rw [Finset.card_le_one]
    intro c₁ hc₁ c₂ hc₂
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hG_iff] at hc₁ hc₂
    rcases hc₁ with ⟨ha1, hb1⟩
    rcases hc₂ with ⟨ha2, hb2⟩
    rcases ha1 with ⟨haL, hc1L, hc1Lk, hga1⟩ | ⟨haL, hc1ge, hma1⟩ | ⟨haL, haLk, hc1L, hga1⟩ | ⟨hage, hc1L, hma1⟩
    · rcases hb1 with ⟨hbL, _, _, hgb1⟩ | ⟨_, hc1ge, _⟩ | ⟨_, _, hc1L', _⟩ | ⟨_, hc1L', _⟩
      · rcases ha2 with ⟨_, hc2L, hc2Lk, hga2⟩ | ⟨_, hc2ge, hma2⟩ | ⟨haL', _, _, _⟩ | ⟨haL', _, _⟩
        · exact Fin.ext (by omega)
        · rcases hb2 with ⟨_, _, hc2Lk, _⟩ | ⟨_, _, hmb2⟩ | ⟨hbL', _, _, _⟩ | ⟨hbL', _, _⟩
          · omega
          · exact absurd (Fin.ext (hgrp_mod_inj a.val b.val haL hbL (hga1.symm.trans hgb1) (hma2.symm.trans hmb2))) hab
          · omega
          · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · rcases hb1 with ⟨_, _, hc1Lk, _⟩ | ⟨hbL, _, hmb1⟩ | ⟨_, _, hc1L', _⟩ | ⟨_, hc1L', _⟩
      · omega
      · rcases ha2 with ⟨_, hc2L, hc2Lk, hga2⟩ | ⟨_, hc2ge, hma2⟩ | ⟨haL', _, _, _⟩ | ⟨haL', _, _⟩
        · rcases hb2 with ⟨_, _, _, hgb2⟩ | ⟨_, hc2ge, _⟩ | ⟨hbL', _, _, _⟩ | ⟨hbL', _, _⟩
          · exact absurd (Fin.ext (hgrp_mod_inj a.val b.val haL hbL (hga2.symm.trans hgb2) (hma1.symm.trans hmb1))) hab
          · omega
          · omega
          · omega
        · exact Fin.ext (by omega)
        · omega
        · omega
      · omega
      · omega
    · rcases hb1 with ⟨hbL, hc1L', _, _⟩ | ⟨hbL, hc1ge, _⟩ | ⟨hbL, hbLk, _, hgb1⟩ | ⟨hbge, _, hmb1⟩
      · omega
      · omega
      · exact absurd (Fin.ext (by omega)) hab
      · rcases ha2 with ⟨haL', _, _, _⟩ | ⟨haL', _, _⟩ | ⟨_, _, hc2L, hga2⟩ | ⟨hage, _, _⟩
        · omega
        · omega
        · rcases hb2 with ⟨hbL, _, _, _⟩ | ⟨hbL, _, _⟩ | ⟨_, hbLk, _, _⟩ | ⟨_, _, hmb2⟩
          · omega
          · omega
          · omega
          · exact Fin.ext (hgrp_mod_inj c₁.val c₂.val hc1L hc2L (hga1.symm.trans hga2) (hmb1.symm.trans hmb2))
        · omega
    · rcases hb1 with ⟨hbL, hc1L', _, _⟩ | ⟨hbL, hc1ge, _⟩ | ⟨hbL, hbLk, _, hgb1⟩ | ⟨hbge, _, hmb1⟩
      · omega
      · omega
      · rcases ha2 with ⟨haL', _, _, _⟩ | ⟨haL', _, _⟩ | ⟨_, haLk, _, _⟩ | ⟨_, hc2L, hma2⟩
        · omega
        · omega
        · omega
        · rcases hb2 with ⟨hbL', _, _, _⟩ | ⟨hbL', _, _⟩ | ⟨_, _, _, hgb2⟩ | ⟨hbge, _, _⟩
          · omega
          · omega
          · exact Fin.ext (hgrp_mod_inj c₁.val c₂.val hc1L hc2L (hgb1.symm.trans hgb2) (hma1.symm.trans hma2))
          · omega
      · exact absurd (Fin.ext (by omega)) hab
  have hrowT : (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤ t := by
    let φ : Fin (t - 1) → Finset (Fin n) := fun p => {⟨L + k + p.val, by omega⟩}
    have hsub : R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true)) ⊆
        insert ∅ (Finset.univ.image φ) := by
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨a, ha, rfl⟩
      have haLk : a.val < L + k := (Finset.mem_filter.mp ha).2
      by_cases haL : a.val < L
      · apply Finset.mem_insert_of_mem
        refine Finset.mem_image.mpr ⟨⟨a.val % (t - 1), Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
        ext c
        simp only [φ, B, Finset.mem_singleton, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and, not_lt, hG_iff]
        constructor
        · rintro rfl
          exact ⟨by dsimp only; omega, Or.inr (Or.inl ⟨haL, by dsimp only; omega, by dsimp only; omega⟩)⟩
        · rintro ⟨hcge, (⟨_, _, hcLk, _⟩ | ⟨_, _, hmod⟩ | ⟨h1, _, _, _⟩ | ⟨h1, _, _⟩)⟩
          · omega
          · exact Fin.ext (by dsimp; omega)
          · omega
          · omega
      · apply Finset.mem_insert.mpr
        left
        ext c
        simp only [B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_lt,
          Finset.notMem_empty, iff_false, not_and, hG_iff]
        intro hcge hG
        rcases hG with ⟨h1, _, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, hcL, _⟩ | ⟨h1, _, _⟩ <;> omega
    calc (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card
        ≤ (insert ∅ (Finset.univ.image φ)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.image φ).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Finset.univ : Finset (Fin (t - 1))).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ = t := by rw [Finset.card_fin]; omega
  have hcolT : (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤ t := by
    have heq : B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true)) =
        R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true)) := by
      ext S
      simp only [Finset.mem_image]
      constructor <;> rintro ⟨x, hx, rfl⟩ <;> refine ⟨x, hx, ?_⟩ <;> ext y <;>
        (simp only [R, B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]; rw [hG_symm])
    rw [heq]
    exact hrowT
  refine ⟨n, n, G, R, B, ⟨hdegR, hdegC, hc4, hrowT, hcolT, true, ?_⟩, ?_⟩
  · intro a ha b hb x hx y hy hax hbx hby
    have haR : a.val < L + k := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have hbR : b.val < L + k := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
    have hxB : x.val < L + k := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hyB : y.val < L + k := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    rw [hG_iff] at hax hbx hby ⊢
    rcases hax with ⟨haL, hxL, hxLk, haxg⟩ | ⟨_, hxge, _⟩ | ⟨haL, haLk, hxL, haxg⟩ | ⟨hage, _, _⟩
    · rcases hbx with ⟨hbL, _, _, hbxg⟩ | ⟨_, hxge, _⟩ | ⟨_, _, hxL', _⟩ | ⟨hbge, _, _⟩
      · rcases hby with ⟨_, hyL, hyLk, hbyg⟩ | ⟨_, hyge, _⟩ | ⟨hbL', _, _, _⟩ | ⟨hbge, _, _⟩
        · exact Or.inl ⟨haL, hyL, hyLk, by omega⟩
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · omega
    · rcases hbx with ⟨_, hxL', _, _⟩ | ⟨_, hxge, _⟩ | ⟨hbL, hbLk, _, hbxg⟩ | ⟨hbge, _, _⟩
      · omega
      · omega
      · rcases hby with ⟨hbL', _, _, _⟩ | ⟨hbL', _, _⟩ | ⟨_, _, hyL, hbyg⟩ | ⟨hbge, _, _⟩
        · omega
        · omega
        · exact Or.inr (Or.inr (Or.inl ⟨haL, haLk, hyL, by omega⟩))
        · omega
      · omega
    · omega
  · rw [hR_card]
    change (L + k) + (L + k) = 2 * L + 2 * k
    omega

private theorem lower_bound_true (d t : Nat) (hd : 2 ≤ d) (ht : 2 ≤ t) :
    ∃ (n m : Nat) (G : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)),
      admissible d t n m G true R B ∧
      R.card + B.card = max (2 * d * t) (2 * (d * (t - 1)) + 2 * (d * (t - 1) / 2)) := by
  let L := d * (t - 1)
  by_cases ht3 : t ≤ 3
  · have hmax : max (2 * d * t) (2 * L + 2 * (L / 2)) = 2 * d * t := by
      apply max_eq_left
      have ht_cases : t = 2 ∨ t = 3 := by omega
      rcases ht_cases with rfl | rfl
      · dsimp [L]; omega
      · dsimp [L]; omega
    rw [hmax]
    exact exists_matching_true d t hd ht
  · have ht4 : 4 ≤ t := by omega
    have hmax : max (2 * d * t) (2 * L + 2 * (L / 2)) = 2 * L + 2 * (L / 2) := by
      apply max_eq_right
      have hdt_ge : 2 ≤ d * (t - 3) := by
        calc 2 = 2 * 1 := by rfl
          _ ≤ d * (t - 3) := Nat.mul_le_mul hd (by omega)
      have h3L : 3 * L = 2 * d * t + d * (t - 3) := by
        have hEq : 3 * (t - 1) = 2 * t + (t - 3) := by omega
        calc 3 * (d * (t - 1)) = d * (3 * (t - 1)) := Nat.mul_left_comm 3 d (t - 1)
          _ = d * (2 * t + (t - 3)) := by rw [hEq]
          _ = d * (2 * t) + d * (t - 3) := Nat.mul_add _ _ _
          _ = 2 * d * t + d * (t - 3) := by rw [Nat.mul_left_comm, ← Nat.mul_assoc]
      omega
    rw [hmax]
    exact exists_stars_true d t hd ht4

private theorem solve_25577 (d t : Nat) (hd : 2 ≤ d) (ht : 2 ≤ t) :
    let L := d * (t - 1)
    let cap := max (2 * d * t) (2 * L + 2 * (L / 2))
    (∀ (n m : Nat) (G : Fin n → Fin m → Bool) (edge : Bool)
        (R : Finset (Fin n)) (B : Finset (Fin m)),
      admissible d t n m G edge R B → R.card + B.card ≤ cap) ∧
    (∀ edge : Bool, ∃ (n m : Nat) (G : Fin n → Fin m → Bool)
        (R : Finset (Fin n)) (B : Finset (Fin m)),
      admissible d t n m G edge R B ∧ R.card + B.card = cap) := by
  refine ⟨?_, ?_⟩
  · intro n m G edge R B hadm
    have hadm' := (admissible_flip d t n m G edge R B).mp hadm
    exact upper_bound_true d t n m (fun a c => G a c == edge) R B hd ht hadm'
  · intro edge
    rcases lower_bound_true d t hd ht with ⟨n, m, G, R, B, hadm, hcard⟩
    refine ⟨n, m, fun a c => G a c == edge, R, B, ?_, hcard⟩
    rw [admissible_flip]
    have hGeq : (fun a c => ((G a c == edge) == edge)) = G := by
      funext a c; cases edge <;> cases G a c <;> decide
    rw [hGeq]
    exact hadm

end PEqualNP.Outside.L_meta_25577_aux

theorem PEqualNP.Outside.L_meta_25577 :
∀ (d t : ℕ), 2 ≤ d → 2 ≤ t →
  let L := d * (t - 1)
  let cap := max (2 * d * t) (2 * L + 2 * (L / 2))
  let admissible := fun (n m : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
      (R : Finset (Fin n)) (B : Finset (Fin m)) =>
    let nbrR := fun (row : Fin n) => Finset.univ.filter (fun dest : Fin m => G row dest = edge)
    let nbrC := fun (col : Fin m) => Finset.univ.filter (fun src : Fin n => G src col = edge)
    let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
    let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
    let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ rowPol)
    let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ colPol)
    (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) ∧
    (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) ∧
    (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) ∧
    rowTypes.card ≤ t ∧ colTypes.card ≤ t ∧
    ∃ mark : Bool, ∀ a ∈ coreRows mark, ∀ b ∈ coreRows mark,
      ∀ x ∈ coreCols mark, ∀ y ∈ coreCols mark,
        G a x = mark → G b x = mark → G b y = mark → G a y = mark
  (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
      (R : Finset (Fin n)) (B : Finset (Fin m)),
    admissible n m G edge R B → R.card + B.card ≤ cap) ∧
  (∀ edge : Bool, ∃ (n m : ℕ) (G : Fin n → Fin m → Bool)
      (R : Finset (Fin n)) (B : Finset (Fin m)),
    admissible n m G edge R B ∧ R.card + B.card = cap) :=
  PEqualNP.Outside.L_meta_25577_aux.solve_25577

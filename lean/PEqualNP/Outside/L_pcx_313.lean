import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_313_aux

open PEqualNP.ProofComplexity

variable {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}

abbrev Raw {n : ℕ} (w : Fin n → ℕ) := (v : Fin n) × Fin (w v)

def par (x : Raw w → Bool) (v : Fin n) : Bool :=
  decide (Odd (((Finset.univ : Finset (Fin (w v))).filter (fun j => x ⟨v, j⟩ = true)).card))

def blk (w : Fin n → ℕ) (S : Finset (Fin n)) : Finset (Raw w) :=
  (Finset.univ : Finset (Raw w)).filter (fun z => z.1 ∈ S)

def rc (X : Finset (Raw w)) (y : Raw w → Bool) : Clause (Raw w) :=
  X.image (fun z => (z, !(y z)))

def bv (C : Clause (Fin n)) : Finset (Fin n) := C.image Prod.fst

def cln (C : Clause (Fin n)) : Prop := ∀ v, ¬ ((v, true) ∈ C ∧ (v, false) ∈ C)

def lifted (w : Fin n → ℕ) (F : Set (Clause (Fin n))) : Set (Clause (Raw w)) :=
  {A | ∃ C ∈ F, ∃ x : Raw w → Bool, (∀ l ∈ C, par x l.1 ≠ l.2) ∧
    A = rc (blk w (C.image Prod.fst)) x}

def RD (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (A : Clause (Raw w)) : Prop :=
  ∃ π : List (Clause (Raw w)), IsDerivation (lifted w F) π ∧ A ∈ π ∧ ∀ C ∈ π, C.card ≤ W

def SD (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (A : Clause (Raw w)) : Prop :=
  ∃ B ⊆ A, RD w F W B

def T (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (C : Clause (Fin n)) : Prop :=
  ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Fin n)),
    [] ∈ N ∧ J ⊆ N ∧ line [] = C ∧
    (∀ (s : List Bool) (b : Bool), s ++ [b] ∈ N → s ∈ J) ∧
    (∀ s ∈ N, cln (line s)) ∧
    (∀ s ∈ N \ J, line s ∈ F ∧ (bv (line s)).sum w ≤ W) ∧
    ∀ s ∈ J, s ++ [false] ∈ N ∧ s ++ [true] ∈ N ∧
      IsResolvent (line (s ++ [false])) (line (s ++ [true])) (line s) ∧
        (bv (line (s ++ [false])) ∪ bv (line (s ++ [true]))).sum w ≤ W + 1

lemma deriv_append {V : Type} [DecidableEq V] {G : Set (Clause V)}
    {π₁ π₂ : List (Clause V)} (h₁ : IsDerivation G π₁) (h₂ : IsDerivation G π₂) :
    IsDerivation G (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

lemma rd_res {A B R : Clause (Raw w)} (h1 : RD w F W A) (h2 : RD w F W B)
    (hres : IsResolvent A B R) (hR : R.card ≤ W) : RD w F W R := by
  obtain ⟨π1, hd1, hm1, hw1⟩ := h1
  obtain ⟨π2, hd2, hm2, hw2⟩ := h2
  refine ⟨R :: (π1 ++ π2), IsDerivation.res (deriv_append hd1 hd2)
    (List.mem_append_left _ hm1) (List.mem_append_right _ hm2) hres, List.mem_cons_self .., ?_⟩
  intro C hC
  rcases List.mem_cons.mp hC with rfl | hC
  · exact hR
  · rcases List.mem_append.mp hC with h | h
    · exact hw1 _ h
    · exact hw2 _ h

lemma sd_mono {A A' : Clause (Raw w)} (h : SD w F W A) (hs : A ⊆ A') : SD w F W A' := by
  obtain ⟨B, hB, hd⟩ := h
  exact ⟨B, hB.trans hs, hd⟩

lemma sd_res {A : Clause (Raw w)} (z : Raw w) (hA : A.card ≤ W)
    (h1 : SD w F W (insert (z, true) A)) (h2 : SD w F W (insert (z, false) A)) :
    SD w F W A := by
  obtain ⟨B1, hB1, hd1⟩ := h1
  obtain ⟨B2, hB2, hd2⟩ := h2
  by_cases ht : (z, true) ∈ B1
  · by_cases hf : (z, false) ∈ B2
    · have hsub : B1.erase (z, true) ∪ B2.erase (z, false) ⊆ A := by
        intro l hl
        rcases Finset.mem_union.mp hl with hl | hl
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          rcases Finset.mem_insert.mp (hB1 hl) with h | h
          · exact absurd h hne
          · exact h
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          rcases Finset.mem_insert.mp (hB2 hl) with h | h
          · exact absurd h hne
          · exact h
      exact ⟨_, hsub, rd_res hd1 hd2 ⟨z, ht, hf, rfl⟩ (le_trans (Finset.card_le_card hsub) hA)⟩
    · refine ⟨B2, ?_, hd2⟩
      intro l hl
      rcases Finset.mem_insert.mp (hB2 hl) with h | h
      · exact absurd (h ▸ hl) hf
      · exact h
  · refine ⟨B1, ?_, hd1⟩
    intro l hl
    rcases Finset.mem_insert.mp (hB1 hl) with h | h
    · exact absurd (h ▸ hl) ht
    · exact h

lemma rc_card (X : Finset (Raw w)) (y : Raw w → Bool) : (rc X y).card = X.card := by
  unfold rc
  exact Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)

lemma mem_rc {X : Finset (Raw w)} {y : Raw w → Bool} {l : Literal (Raw w)} :
    l ∈ rc X y ↔ l.1 ∈ X ∧ l.2 = !y l.1 := by
  obtain ⟨z, b⟩ := l
  simp only [rc, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨z, ha, rfl, rfl⟩

lemma rc_insert (z : Raw w) (X : Finset (Raw w)) (y : Raw w → Bool) :
    rc (insert z X) y = insert (z, !y z) (rc X y) := by
  unfold rc
  rw [Finset.image_insert]

lemma rc_congr {X : Finset (Raw w)} {y y' : Raw w → Bool} (h : ∀ z ∈ X, y z = y' z) :
    rc X y = rc X y' := by
  unfold rc
  apply Finset.image_congr
  intro z hz
  simp [h z hz]

lemma rc_mono {X X' : Finset (Raw w)} (y : Raw w → Bool) (h : X ⊆ X') : rc X y ⊆ rc X' y :=
  Finset.image_subset_image h

lemma rc_vars (X : Finset (Raw w)) (y : Raw w → Bool) : (rc X y).image Prod.fst = X := by
  ext z
  simp only [rc, Finset.mem_image]
  constructor
  · rintro ⟨l, ⟨a, ha, rfl⟩, rfl⟩
    exact ha
  · intro hz
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

lemma mem_blk {S : Finset (Fin n)} {z : Raw w} : z ∈ blk w S ↔ z.1 ∈ S := by
  simp [blk]

lemma blk_card (S : Finset (Fin n)) : (blk w S).card = S.sum w := by
  have : blk w S = S.sigma (fun v => (Finset.univ : Finset (Fin (w v)))) := by
    ext ⟨v, j⟩
    simp [blk]
  rw [this, Finset.card_sigma]
  simp

lemma par_congr {y y' : Raw w → Bool} {v : Fin n} (h : ∀ j, y ⟨v, j⟩ = y' ⟨v, j⟩) :
    par y v = par y' v := by
  simp only [par, h]

lemma par_update_ne {y : Raw w → Bool} {z : Raw w} {v : Fin n} (b : Bool) (hz : z.1 ≠ v) :
    par (Function.update y z b) v = par y v := by
  apply par_congr
  intro j
  apply Function.update_of_ne
  intro h
  apply hz
  subst h
  rfl

lemma par_update_self (y : Raw w → Bool) (z : Raw w) :
    par (Function.update y z true) z.1 = !par (Function.update y z false) z.1 := by
  obtain ⟨v, j0⟩ := z
  unfold par
  have h1 : ((Finset.univ : Finset (Fin (w v))).filter
      fun j => Function.update y ⟨v, j0⟩ true ⟨v, j⟩ = true) =
      insert j0 ((Finset.univ : Finset (Fin (w v))).filter
      fun j => Function.update y ⟨v, j0⟩ false ⟨v, j⟩ = true) := by
    ext j
    by_cases hj : j = j0
    · subst hj
      simp
    · have hne : (⟨v, j⟩ : Raw w) ≠ ⟨v, j0⟩ := by
        intro h
        apply hj
        simpa using h
      simp [hj]
  have h0 : j0 ∉ ((Finset.univ : Finset (Fin (w v))).filter
      fun j => Function.update y ⟨v, j0⟩ false ⟨v, j⟩ = true) := by
    simp
  simp only
  rw [h1, Finset.card_insert_of_notMem h0]
  simp only [Nat.odd_add_one, decide_not]

def Lift (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (D : Clause (Fin n)) : Prop :=
  ∀ x : Raw w → Bool, (∀ l ∈ D, par x l.1 ≠ l.2) → SD w F W (rc (blk w (bv D)) x)

lemma lift_leaf {D : Clause (Fin n)} (hF : D ∈ F) (hW : (bv D).sum w ≤ W) : Lift w F W D := by
  intro x hx
  refine ⟨_, subset_refl _, [rc (blk w (bv D)) x],
    IsDerivation.ax IsDerivation.nil ⟨D, hF, x, hx, rfl⟩, List.mem_singleton_self _, ?_⟩
  intro C hC
  rw [List.mem_singleton.mp hC, rc_card, blk_card]
  exact hW

lemma sd_elim (G : Finset (Raw w)) (Ok : (Raw w → Bool) → Prop) :
    ∀ X : Finset (Raw w), Disjoint G X →
      (∀ y z b, z ∈ X → Ok y → Ok (Function.update y z b)) →
      G.card + X.card ≤ W + 1 → (∀ y, Ok y → SD w F W (rc (G ∪ X) y)) →
      ∀ y, Ok y → SD w F W (rc G y) := by
  intro X
  induction X using Finset.induction_on with
  | empty =>
    intro _ _ _ h y hy
    simpa using h y hy
  | insert z X hz ih =>
    intro hdis hok hcard h
    have hcard' : G.card + X.card + 1 ≤ W + 1 := by
      rw [Finset.card_insert_of_notMem hz] at hcard
      omega
    apply ih (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdis)
      (fun y z' b hz' hy => hok y z' b (Finset.mem_insert_of_mem hz') hy) (by omega)
    intro y hy
    have hzG : z ∉ G := fun h => Finset.disjoint_left.mp hdis h (Finset.mem_insert_self _ _)
    have hzGX : z ∉ G ∪ X := by simp [hzG, hz]
    have hcongr : ∀ b, rc (G ∪ X) (Function.update y z b) = rc (G ∪ X) y := fun b =>
      rc_congr (fun z' hz' => Function.update_of_ne (fun h => hzGX (by rw [← h]; exact hz')) _ _)
    have hins : ∀ b, rc (G ∪ insert z X) (Function.update y z b) =
        insert (z, !b) (rc (G ∪ X) y) := by
      intro b
      rw [Finset.union_insert, rc_insert, hcongr]
      simp
    apply sd_res z
    · rw [rc_card]
      have := Finset.card_union_le G X
      omega
    · have := h _ (hok y z false (Finset.mem_insert_self _ _) hy)
      rw [hins] at this
      simpa using this
    · have := h _ (hok y z true (Finset.mem_insert_self _ _) hy)
      rw [hins] at this
      simpa using this

lemma lift_step {P Q R : Clause (Fin n)} (hP : Lift w F W P) (hQ : Lift w F W Q)
    (hcP : cln P) (hcQ : cln Q) (hres : IsResolvent P Q R)
    (hwt : (bv P ∪ bv Q).sum w ≤ W + 1) : Lift w F W R := by
  obtain ⟨v, hvP, hvQ, rfl⟩ := hres
  have hvR : v ∉ bv (P.erase (v, true) ∪ Q.erase (v, false)) := by
    intro h
    obtain ⟨⟨u, s⟩, hl, hu⟩ := Finset.mem_image.mp h
    simp only at hu
    subst hu
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      cases s
      · exact hcP u ⟨hvP, hl⟩
      · exact hne rfl
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      cases s
      · exact hne rfl
      · exact hcQ u ⟨hl, hvQ⟩
  have hPsub : bv P ⊆ insert v (bv (P.erase (v, true) ∪ Q.erase (v, false))) := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
    by_cases h : l = (v, true)
    · subst h
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩)))
  have hQsub : bv Q ⊆ insert v (bv (P.erase (v, true) ∪ Q.erase (v, false))) := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
    by_cases h : l = (v, false)
    · subst h
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hl⟩)))
  have hRsub : insert v (bv (P.erase (v, true) ∪ Q.erase (v, false))) ⊆ bv P ∪ bv Q := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hvP)
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
      rcases Finset.mem_union.mp hl with hl | hl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase hl))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase hl))
  intro x hx
  set R := P.erase (v, true) ∪ Q.erase (v, false) with hR
  refine sd_elim (blk w (bv R)) (fun y => ∀ z ∈ blk w (bv R), y z = x z) (blk w {v})
    ?_ ?_ ?_ ?_ x (fun _ _ => rfl)
  · rw [Finset.disjoint_left]
    intro z h1 h2
    rw [mem_blk] at h1 h2
    rw [Finset.mem_singleton] at h2
    exact hvR (h2 ▸ h1)
  · intro y z b hz hy z' hz'
    have hne : z' ≠ z := by
      intro h
      subst h
      rw [mem_blk] at hz hz'
      rw [Finset.mem_singleton] at hz
      exact hvR (hz ▸ hz')
    rw [Function.update_of_ne hne]
    exact hy z' hz'
  · rw [blk_card, blk_card, Finset.sum_singleton, add_comm, ← Finset.sum_insert hvR]
    exact le_trans (Finset.sum_le_sum_of_subset hRsub) hwt
  · intro y hy
    have hfR : ∀ l ∈ R, par y l.1 ≠ l.2 := by
      intro l hl
      rw [par_congr (y' := x) (fun j => hy _ (mem_blk.mpr (Finset.mem_image_of_mem _ hl)))]
      exact hx l hl
    cases hpv : par y v
    · have hfP : ∀ l ∈ P, par y l.1 ≠ l.2 := by
        intro l hl
        by_cases h : l = (v, true)
        · subst h
          simp [hpv]
        · exact hfR l (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩))
      apply sd_mono (hP y hfP)
      apply rc_mono
      intro z hz
      rw [mem_blk] at hz
      rcases Finset.mem_insert.mp (hPsub hz) with h | h
      · exact Finset.mem_union_right _ (mem_blk.mpr (Finset.mem_singleton.mpr h))
      · exact Finset.mem_union_left _ (mem_blk.mpr h)
    · have hfQ : ∀ l ∈ Q, par y l.1 ≠ l.2 := by
        intro l hl
        by_cases h : l = (v, false)
        · subst h
          simp [hpv]
        · exact hfR l (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hl⟩))
      apply sd_mono (hQ y hfQ)
      apply rc_mono
      intro z hz
      rw [mem_blk] at hz
      rcases Finset.mem_insert.mp (hQsub hz) with h | h
      · exact Finset.mem_union_right _ (mem_blk.mpr (Finset.mem_singleton.mpr h))
      · exact Finset.mem_union_left _ (mem_blk.mpr h)

lemma dir1 (hT : T w F W ∅) :
    ∃ π : List (Clause (Raw w)), IsRefutation (lifted w F) π ∧ ∀ C ∈ π, C.card ≤ W := by
  obtain ⟨N, J, line, h0, hJ, hroot, hpar, hcl, hleaf, hint⟩ := hT
  have hall : ∀ k, ∀ s ∈ N, N.sup List.length ≤ s.length + k → Lift w F W (line s) := by
    intro k
    induction k with
    | zero =>
      intro s hs hk
      by_cases hsJ : s ∈ J
      · have h1 := Finset.le_sup (f := List.length) (hint s hsJ).1
        simp only [List.length_append, List.length_singleton] at h1
        omega
      · have := hleaf s (Finset.mem_sdiff.mpr ⟨hs, hsJ⟩)
        exact lift_leaf this.1 this.2
    | succ k ih =>
      intro s hs hk
      by_cases hsJ : s ∈ J
      · obtain ⟨hf, ht, hres, hwt⟩ := hint s hsJ
        exact lift_step (ih _ hf (by simp only [List.length_append, List.length_singleton]; omega)) (ih _ ht (by simp only [List.length_append, List.length_singleton]; omega))
          (hcl _ hf) (hcl _ ht) hres hwt
      · have := hleaf s (Finset.mem_sdiff.mpr ⟨hs, hsJ⟩)
        exact lift_leaf this.1 this.2
  have hL := hall (N.sup List.length) [] h0 (by simp)
  rw [hroot] at hL
  obtain ⟨B, hB, π, hπ, hBπ, hW⟩ := hL (fun _ => false) (by simp)
  have hE : rc (blk w (bv (∅ : Clause (Fin n)))) (fun _ => false) = ∅ := by
    simp [rc, bv, blk]
  rw [hE] at hB
  have : B = ∅ := Finset.subset_empty.mp hB
  subst this
  exact ⟨π, ⟨hπ, hBπ⟩, hW⟩

def glue (R : Clause (Fin n)) (l1 l2 : List Bool → Clause (Fin n)) :
    List Bool → Clause (Fin n)
  | [] => R
  | false :: q => l1 q
  | true :: q => l2 q

lemma T_leaf {C : Clause (Fin n)} (hF : C ∈ F) (hc : cln C) (hW : (bv C).sum w ≤ W) :
    T w F W C := by
  refine ⟨{[]}, ∅, fun _ => C, Finset.mem_singleton_self _, Finset.empty_subset _, rfl,
    ?_, fun _ _ => hc, fun _ _ => ⟨hF, hW⟩, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  intro s b hs
  rw [Finset.mem_singleton] at hs
  exact absurd hs (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

lemma T_clean {C : Clause (Fin n)} (h : T w F W C) : cln C := by
  obtain ⟨N, J, line, h0, _, hroot, _, hcl, _⟩ := h
  exact hroot ▸ hcl [] h0

lemma T_res {P Q R : Clause (Fin n)} (h1 : T w F W P) (h2 : T w F W Q)
    (hres : IsResolvent P Q R) (hc : cln R) (hwt : (bv P ∪ bv Q).sum w ≤ W + 1) :
    T w F W R := by
  obtain ⟨N₁, J₁, line₁, h01, hJ1, hroot1, hpar1, hcl1, hleaf1, hint1⟩ := h1
  obtain ⟨N₂, J₂, line₂, h02, hJ2, hroot2, hpar2, hcl2, hleaf2, hint2⟩ := h2
  let N : Finset (List Bool) := insert [] (N₁.image (false :: ·) ∪ N₂.image (true :: ·))
  let J : Finset (List Bool) := insert [] (J₁.image (false :: ·) ∪ J₂.image (true :: ·))
  refine ⟨N, J, glue R line₁ line₂, Finset.mem_insert_self _ _, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [J, N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · left; rfl
    · right; left; exact ⟨q, hJ1 hq, rfl⟩
    · right; right; exact ⟨q, hJ2 hq, rfl⟩
  · intro p b hp
    simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with hnil | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
    · exact absurd hnil (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
    · cases p with
      | nil => exact Finset.mem_insert_self _ _
      | cons c r =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hpar1 r b hq, rfl⟩))
    · cases p with
      | nil => exact Finset.mem_insert_self _ _
      | cons c r =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hpar2 r b hq, rfl⟩))
  · intro p hp
    simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact hc
    · exact hcl1 q hq
    · exact hcl2 q hq
  · intro p hp
    rw [Finset.mem_sdiff] at hp
    rcases hp with ⟨hpN, hpJ⟩
    simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hpN
    rcases hpN with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact absurd (Finset.mem_insert_self _ _) hpJ
    · apply hleaf1 q
      rw [Finset.mem_sdiff]
      exact ⟨hq, fun hqJ => hpJ (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hqJ, rfl⟩)))⟩
    · apply hleaf2 q
      rw [Finset.mem_sdiff]
      exact ⟨hq, fun hqJ => hpJ (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hqJ, rfl⟩)))⟩
  · intro p hp
    simp only [J, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], h01, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], h02, rfl⟩)),
        ?_, ?_⟩
      · simpa [glue, hroot1, hroot2] using hres
      · simpa [glue, hroot1, hroot2] using hwt
    · obtain ⟨hf, ht, hr, hw'⟩ := hint1 q hq
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hf, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, ht, rfl⟩)),
        by simpa [glue] using hr, by simpa [glue] using hw'⟩
    · obtain ⟨hf, ht, hr, hw'⟩ := hint2 q hq
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hf, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ht, rfl⟩)),
        by simpa [glue] using hr, by simpa [glue] using hw'⟩

def Full (D : Finset (Raw w)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => ∀ j : Fin (w v), (⟨v, j⟩ : Raw w) ∈ D)

def Good (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (D : Finset (Raw w))
    (y : Raw w → Bool) : Prop :=
  ∀ C, T w F W C → bv C ⊆ Full D → ∃ l ∈ C, par y l.1 = l.2

lemma full_mono {D D' : Finset (Raw w)} (h : D' ⊆ D) : Full D' ⊆ Full D := by
  intro v hv
  simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact fun j => h (hv j)

lemma good_mono {D D' : Finset (Raw w)} {y : Raw w → Bool} (h : D' ⊆ D)
    (hG : Good w F W D y) : Good w F W D' y :=
  fun C hC hs => hG C hC (hs.trans (full_mono h))

lemma full_weight (D : Finset (Raw w)) : (Full D).sum w ≤ D.card := by
  rw [← blk_card]
  apply Finset.card_le_card
  intro z hz
  rw [mem_blk] at hz
  simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  exact hz z.2

lemma full_insert {D : Finset (Raw w)} {z : Raw w} {u : Fin n} (h : u ∈ Full (insert z D))
    (hne : u ≠ z.1) : u ∈ Full D := by
  simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  intro j
  rcases Finset.mem_insert.mp (h j) with h' | h'
  · exact absurd (congrArg Sigma.fst h') hne
  · exact h'

def Bad (w : Fin n → ℕ) (F : Set (Clause (Fin n))) (W : ℕ) (D : Finset (Raw w))
    (y : Raw w → Bool) (z : Raw w) (C : Clause (Fin n)) (c : Bool) : Prop :=
  T w F W C ∧ bv C ⊆ Full (insert z D) ∧ (∀ l ∈ C, l.1 ≠ z.1 → par y l.1 ≠ l.2) ∧
    (∀ l ∈ C, l.1 = z.1 → l.2 = c) ∧ ∃ s, (z.1, s) ∈ C

lemma ext_core {D : Finset (Raw w)} {y : Raw w → Bool} (hG : Good w F W D y) {z : Raw w}
    (hz : z ∉ D) (hD : D.card ≤ W) {P Q : Clause (Fin n)}
    (hP : Bad w F W D y z P true) (hQ : Bad w F W D y z Q false) : False := by
  obtain ⟨hTP, hsP, hfP, hcP, sP, hsPm⟩ := hP
  obtain ⟨hTQ, hsQ, hfQ, hcQ, sQ, hsQm⟩ := hQ
  have hvP : (z.1, true) ∈ P := by
    have := hcP _ hsPm rfl
    simp only at this
    exact this ▸ hsPm
  have hvQ : (z.1, false) ∈ Q := by
    have := hcQ _ hsQm rfl
    simp only at this
    exact this ▸ hsQm
  set R := P.erase (z.1, true) ∪ Q.erase (z.1, false) with hR
  have hfR : ∀ l ∈ R, l.1 ≠ z.1 ∧ par y l.1 ≠ l.2 := by
    intro l hl
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      have h1 : l.1 ≠ z.1 := by
        intro h
        apply hne
        exact Prod.ext h (hcP l hl h)
      exact ⟨h1, hfP l hl h1⟩
    · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
      have h1 : l.1 ≠ z.1 := by
        intro h
        apply hne
        exact Prod.ext h (hcQ l hl h)
      exact ⟨h1, hfQ l hl h1⟩
  have hcR : cln R := by
    intro u ⟨h1, h2⟩
    have a := (hfR _ h1).2
    have b := (hfR _ h2).2
    simp only at a b
    cases hp : par y u <;> simp_all
  have hwt : (bv P ∪ bv Q).sum w ≤ W + 1 := by
    calc (bv P ∪ bv Q).sum w ≤ (Full (insert z D)).sum w :=
          Finset.sum_le_sum_of_subset (Finset.union_subset hsP hsQ)
      _ ≤ (insert z D).card := full_weight _
      _ ≤ W + 1 := by rw [Finset.card_insert_of_notMem hz]; omega
  have hTR := T_res hTP hTQ ⟨z.1, hvP, hvQ, rfl⟩ hcR hwt
  have hsub : bv R ⊆ Full D := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
    have hne := (hfR l hl).1
    have hmem : l.1 ∈ Full (insert z D) := by
      rcases Finset.mem_union.mp hl with h | h
      · exact hsP (Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase h))
      · exact hsQ (Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase h))
    exact full_insert hmem hne
  obtain ⟨l, hl, hpar⟩ := hG R hTR hsub
  exact (hfR l hl).2 hpar

lemma bad_of_not_good {D : Finset (Raw w)} {y : Raw w → Bool} (hG : Good w F W D y)
    {z : Raw w} (b : Bool) (h : ¬ Good w F W (insert z D) (Function.update y z b)) :
    ∃ C, Bad w F W D y z C (!par (Function.update y z b) z.1) := by
  unfold Good at h
  push_neg at h
  obtain ⟨C, hT, hsub, hf⟩ := h
  have h1 : ∀ l ∈ C, l.1 ≠ z.1 → par y l.1 ≠ l.2 := by
    intro l hl hne
    rw [← par_update_ne b (Ne.symm hne)]
    exact hf l hl
  refine ⟨C, hT, hsub, h1, ?_, ?_⟩
  · intro l hl he
    have := hf l hl
    rw [he] at this
    revert this
    cases l.2 <;> cases par (Function.update y z b) z.1 <;> simp
  · by_contra hno
    push_neg at hno
    have hsD : bv C ⊆ Full D := by
      intro u hu
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
      have hne : l.1 ≠ z.1 := by
        intro he
        apply hno l.2
        rw [← he]
        exact hl
      exact full_insert (hsub (Finset.mem_image_of_mem _ hl)) hne
    obtain ⟨l, hl, hp⟩ := hG C hT hsD
    have hne : l.1 ≠ z.1 := by
      intro he
      apply hno l.2
      rw [← he]
      exact hl
    exact h1 l hl hne hp

lemma good_ext {D : Finset (Raw w)} {y : Raw w → Bool} (hG : Good w F W D y) {z : Raw w}
    (hz : z ∉ D) (hD : D.card ≤ W) :
    ∃ b, Good w F W (insert z D) (Function.update y z b) := by
  by_contra hne
  push_neg at hne
  obtain ⟨C0, h0⟩ := bad_of_not_good hG false (hne false)
  obtain ⟨C1, h1⟩ := bad_of_not_good hG true (hne true)
  rw [par_update_self] at h1
  cases hp : par (Function.update y z false) z.1
  · rw [hp] at h0 h1
    exact ext_core hG hz hD (P := C0) (Q := C1) (by simpa using h0) (by simpa using h1)
  · rw [hp] at h0 h1
    exact ext_core hG hz hD (P := C1) (Q := C0) (by simpa using h1) (by simpa using h0)

lemma dir2_inv {π : List (Clause (Raw w))} (hπ : IsDerivation (lifted w F) π) :
    (∀ C ∈ π, C.card ≤ W) →
    ∀ A ∈ π, ∀ y, Good w F W (A.image Prod.fst) y → ∃ l ∈ A, y l.1 = l.2 := by
  induction hπ with
  | nil =>
    intro _ A hA
    simp at hA
  | @ax π' A0 _ hC ih =>
    intro hW A hA y hG
    have hW' : ∀ C ∈ π', C.card ≤ W := fun C h => hW C (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp hA with rfl | hA
    · by_contra hno
      push_neg at hno
      have hcard := hW _ (List.mem_cons_self ..)
      obtain ⟨D, hD, x, hx, rfl⟩ := hC
      have hyx : ∀ z ∈ blk w (D.image Prod.fst), y z = x z := by
        intro z hz
        have := hno (z, !x z) (mem_rc.mpr ⟨hz, rfl⟩)
        simpa using this
      have hcl : cln D := by
        intro v ⟨h1, h2⟩
        have a := hx _ h1
        have b := hx _ h2
        simp only at a b
        cases h : par x v <;> simp_all
      rw [rc_card, blk_card] at hcard
      have hTD : T w F W D := T_leaf hD hcl hcard
      have hsub : bv D ⊆ Full ((rc (blk w (D.image Prod.fst)) x).image Prod.fst) := by
        rw [rc_vars]
        intro v hv
        simp only [Full, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j
        exact mem_blk.mpr hv
      obtain ⟨l, hl, hpl⟩ := hG D hTD hsub
      apply hx l hl
      rw [← hpl]
      symm
      apply par_congr
      intro j
      apply hyx
      exact mem_blk.mpr (Finset.mem_image_of_mem _ hl)
    · exact ih hW' A hA y hG
  | @res π' C D R _ hC hD hres ih =>
    intro hW A hA y hG
    have hW' : ∀ C ∈ π', C.card ≤ W := fun C h => hW C (List.mem_cons_of_mem _ h)
    have hRW : R.card ≤ W := hW _ (List.mem_cons_self ..)
    obtain ⟨z, hzC, hzD, rfl⟩ := hres
    rcases List.mem_cons.mp hA with rfl | hA
    · set R := C.erase (z, true) ∪ D.erase (z, false) with hR
      by_contra hno
      push_neg at hno
      obtain ⟨y', hG', hf'⟩ : ∃ y', Good w F W (insert z (R.image Prod.fst)) y' ∧
          ∀ l ∈ R, y' l.1 ≠ l.2 := by
        by_cases hz : z ∈ R.image Prod.fst
        · exact ⟨y, by rw [Finset.insert_eq_of_mem hz]; exact hG, hno⟩
        · obtain ⟨b, hb⟩ := good_ext hG hz (le_trans Finset.card_image_le hRW)
          refine ⟨_, hb, ?_⟩
          intro l hl
          have hne : l.1 ≠ z := fun h => hz (h ▸ Finset.mem_image_of_mem _ hl)
          rw [Function.update_of_ne hne]
          exact hno l hl
      have hCs : C.image Prod.fst ⊆ insert z (R.image Prod.fst) := by
        intro u hu
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
        by_cases h : l = (z, true)
        · rw [h]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩)))
      have hDs : D.image Prod.fst ⊆ insert z (R.image Prod.fst) := by
        intro u hu
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
        by_cases h : l = (z, false)
        · rw [h]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hl⟩)))
      obtain ⟨l1, hl1, h1⟩ := ih hW' C hC y' (good_mono hCs hG')
      obtain ⟨l2, hl2, h2⟩ := ih hW' D hD y' (good_mono hDs hG')
      cases hyz : y' z
      · by_cases h : l1 = (z, true)
        · subst h
          simp_all
        · exact hf' l1 (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl1⟩)) h1
      · by_cases h : l2 = (z, false)
        · subst h
          simp_all
        · exact hf' l2 (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hl2⟩)) h2
    · exact ih hW' A hA y hG

lemma dir2 (hw : ∀ v, 0 < w v) {π : List (Clause (Raw w))}
    (hπ : IsRefutation (lifted w F) π) (hW : ∀ C ∈ π, C.card ≤ W) : T w F W ∅ := by
  by_contra hT
  have hG : Good w F W ((∅ : Clause (Raw w)).image Prod.fst) (fun _ => false) := by
    intro C hC hsub
    exfalso
    have hFull : Full (w := w) ((∅ : Clause (Raw w)).image Prod.fst) = ∅ := by
      ext v
      simp only [Full, Finset.image_empty, Finset.notMem_empty, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_false, not_forall]
      exact ⟨⟨0, hw v⟩, id⟩
    have hC0 : C = ∅ := by
      rw [hFull] at hsub
      ext l
      simp only [Finset.notMem_empty, iff_false]
      intro hl
      exact Finset.notMem_empty _ (hsub (Finset.mem_image_of_mem _ hl))
    exact hT (hC0 ▸ hC)
  obtain ⟨l, hl, _⟩ := dir2_inv hπ.1 hW ∅ hπ.2 _ hG
  simp at hl

theorem derivation_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π₁ π₂ : List (Clause V)} (h₁ : IsDerivation F π₁) (h₂ : IsDerivation F π₂) :
    IsDerivation F (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

theorem completeness_aux {V : Type} [DecidableEq V] (F : Set (Clause V)) (S : Finset V) :
    ∀ a : V → Bool,
      (∀ b : V → Bool, (∀ v, v ∉ S → b v = a v) → ∃ C ∈ F, ¬ ClauseSat b C) →
      ∃ π : List (Clause V), IsDerivation F π ∧ π.length + 1 ≤ 2 ^ (S.card + 1) ∧
        ∃ C ∈ π, (∀ l ∈ C, a l.1 ≠ l.2) ∧ ∀ l ∈ C, l.1 ∉ S := by
  induction S using Finset.induction_on with
  | empty =>
    intro a h
    obtain ⟨C, hCF, hC⟩ := h a (fun _ _ => rfl)
    refine ⟨[C], IsDerivation.ax IsDerivation.nil hCF, by simp, C, by simp, ?_, by simp⟩
    intro l hl hal
    exact hC ⟨l, hl, hal⟩
  | insert x S hx ih =>
    intro a h
    have hsub : ∀ t : Bool, ∀ b : V → Bool, (∀ v, v ∉ S → b v = Function.update a x t v) →
        ∃ C ∈ F, ¬ ClauseSat b C := by
      intro t b hb
      apply h b
      intro v hv
      have hvx : v ≠ x := fun e => hv (e ▸ Finset.mem_insert_self x S)
      have hvS : v ∉ S := fun e => hv (Finset.mem_insert_of_mem e)
      rw [hb v hvS, Function.update_of_ne hvx]
    obtain ⟨π₀, hπ₀, hlen₀, C₀, hC₀π, hC₀a, hC₀S⟩ := ih (Function.update a x false) (hsub false)
    obtain ⟨π₁, hπ₁, hlen₁, C₁, hC₁π, hC₁a, hC₁S⟩ := ih (Function.update a x true) (hsub true)
    have hpow : 2 ^ ((insert x S).card + 1) = 2 * 2 ^ (S.card + 1) := by
      rw [Finset.card_insert_of_notMem hx, pow_succ, mul_comm]

    have key : ∀ (t : Bool) (C : Clause V), (∀ l ∈ C, Function.update a x t l.1 ≠ l.2) →
        (∀ l ∈ C, l.1 ∉ S) → ∀ l ∈ C, l.1 ≠ x → a l.1 ≠ l.2 ∧ l.1 ∉ insert x S := by
      intro t C hCa hCS l hl hlx
      refine ⟨?_, ?_⟩
      · have := hCa l hl
        rwa [Function.update_of_ne hlx] at this
      · intro hmem
        rcases Finset.mem_insert.mp hmem with e | e
        · exact hlx e
        · exact hCS l hl e

    have onx : ∀ (t : Bool) (C : Clause V), (∀ l ∈ C, Function.update a x t l.1 ≠ l.2) →
        ∀ l ∈ C, l.1 = x → l = (x, !t) := by
      intro t C hCa l hl hlx
      have := hCa l hl
      rw [hlx, Function.update_self] at this
      obtain ⟨v, s⟩ := l
      simp only at hlx this
      subst hlx
      cases t <;> cases s <;> simp_all
    by_cases h₀ : (x, true) ∈ C₀
    · by_cases h₁ : (x, false) ∈ C₁
      · refine ⟨(C₀.erase (x, true) ∪ C₁.erase (x, false)) :: (π₀ ++ π₁), ?_, ?_, _,
          List.mem_cons_self, ?_, ?_⟩
        · exact IsDerivation.res (derivation_append hπ₀ hπ₁) (List.mem_append_left _ hC₀π)
            (List.mem_append_right _ hC₁π) ⟨x, h₀, h₁, rfl⟩
        · rw [hpow]; simp only [List.length_cons, List.length_append]; omega
        · intro l hl
          rcases Finset.mem_union.mp hl with hl | hl
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx false C₀ hC₀a l hl e)
            exact (key false C₀ hC₀a hC₀S l hl hlx).1
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx true C₁ hC₁a l hl e)
            exact (key true C₁ hC₁a hC₁S l hl hlx).1
        · intro l hl
          rcases Finset.mem_union.mp hl with hl | hl
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx false C₀ hC₀a l hl e)
            exact (key false C₀ hC₀a hC₀S l hl hlx).2
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx true C₁ hC₁a l hl e)
            exact (key true C₁ hC₁a hC₁S l hl hlx).2
      · have hnox : ∀ l ∈ C₁, l.1 ≠ x := by
          intro l hl e
          have := onx true C₁ hC₁a l hl e
          simp at this
          exact h₁ (this ▸ hl)
        refine ⟨π₁, hπ₁, by rw [hpow]; omega, C₁, hC₁π, ?_, ?_⟩
        · exact fun l hl => (key true C₁ hC₁a hC₁S l hl (hnox l hl)).1
        · exact fun l hl => (key true C₁ hC₁a hC₁S l hl (hnox l hl)).2
    · have hnox : ∀ l ∈ C₀, l.1 ≠ x := by
        intro l hl e
        have := onx false C₀ hC₀a l hl e
        simp at this
        exact h₀ (this ▸ hl)
      refine ⟨π₀, hπ₀, by rw [hpow]; omega, C₀, hC₀π, ?_, ?_⟩
      · exact fun l hl => (key false C₀ hC₀a hC₀S l hl (hnox l hl)).1
      · exact fun l hl => (key false C₀ hC₀a hC₀S l hl (hnox l hl)).2

theorem completeness {V : Type} [DecidableEq V] [Fintype V] (F : Set (Clause V))
    (h : ¬ Satisfiable F) :
    ∃ π : List (Clause V), IsRefutation F π ∧ π.length ≤ 2 ^ (Fintype.card V + 1) - 1 := by
  have hF : ∀ b : V → Bool, ∃ C ∈ F, ¬ ClauseSat b C := by
    intro b
    by_contra hb
    exact h ⟨b, fun C hC => by_contra fun hn => hb ⟨C, hC, hn⟩⟩
  obtain ⟨π, hπ, hlen, C, hCπ, -, hCS⟩ :=
    completeness_aux F Finset.univ (fun _ => false) (fun b _ => hF b)
  have hC : C = ∅ := Finset.eq_empty_of_forall_notMem fun l hl => hCS l hl (Finset.mem_univ _)
  refine ⟨π, ⟨hπ, hC ▸ hCπ⟩, ?_⟩
  rw [Finset.card_univ] at hlen
  omega

abbrev Tree (n : ℕ) := Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Fin n))

def goodTree {n : ℕ} (F : Set (Clause (Fin n))) (z : Tree n) := ∃ (N J : Finset (List Bool)) (line : List Bool→ Clause (Fin n)),
  z=(N,J,line) ∧ []∈N ∧ J⊆N ∧ line []=∅ ∧
  (∀ s b,s++[b]∈N→s∈J) ∧ (∀ s∈N,cln (line s)) ∧
  (∀ s∈N\J,line s∈F) ∧
  ∀ s∈J,s++[false]∈N ∧ s++[true]∈N ∧ IsResolvent (line (s++[false])) (line (s++[true])) (line s)

def cost (t : ℕ) (q : ℕ×ℕ) := t*q.1+q.2

def toll {n : ℕ} (a b : Fin n→ℕ) (A : Finset (Fin n)) (delta : ℕ) : ℕ×ℕ := (A.sum a,A.sum b+delta)

def tolls {n : ℕ} (a b : Fin n→ℕ) (z : Tree n) : Finset (ℕ×ℕ) :=
  insert (0,1) (((z.1\z.2.1).image (fun i=>toll a b (bv (z.2.2 i)) 1)) ∪
    (z.2.1.image (fun i=>toll a b (bv (z.2.2 (i++[false])) ∪ bv (z.2.2 (i++[true]))) 0)))

theorem toll_cost {n : ℕ} (t : ℕ) (a b : Fin n→ℕ) (A : Finset (Fin n)) (d : ℕ) :
    cost t (toll a b A d)= A.sum (fun i=>t*a i+b i)+d := by
  simp [cost,toll,Finset.sum_add_distrib,Finset.mul_sum,add_assoc]

theorem test_tolls {n : ℕ} (t W : ℕ) (a b : Fin n→ℕ) (N J : Finset (List Bool)) (line : List Bool→ Clause (Fin n)) :
    (∀ q∈tolls a b (N,J,line),cost t q ≤ W+1) ↔
      (∀ p∈N\J,(bv (line p)).sum (fun v=>t*a v+b v) ≤ W) ∧
      ∀ p∈J,(bv (line (p++[false]))∪bv (line (p++[true]))).sum (fun v=>t*a v+b v) ≤ W+1 := by
  classical
  constructor
  · intro h
    constructor
    · intro p hp
      have here : toll a b (bv (line p)) 1 ∈ tolls a b (N,J,line) :=
        Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
      simpa only [toll_cost,Nat.add_le_add_iff_right] using h _ here
    · intro p hp
      have here : toll a b (bv (line (p++[false])) ∪ bv (line (p++[true]))) 0 ∈ tolls a b (N,J,line) :=
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
      simpa only [toll_cost,Nat.add_zero] using h _ here
  · rintro ⟨lf,jn⟩ q hq
    rcases Finset.mem_insert.mp hq with eq|h
    · simp [eq,cost]
    rcases Finset.mem_union.mp h with l|j
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp l
      simpa only [toll_cost,Nat.add_le_add_iff_right] using lf p hp
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp j
      simpa only [toll_cost,Nat.add_zero] using jn p hp

theorem smallTree {n : ℕ} (t W : ℕ) (a b : Fin n→ℕ) (F : Set (Clause (Fin n))) :
    T (fun v=>t*a v+b v) F W ∅ ↔ ∃ z : Tree n, goodTree F z ∧ ∀ q∈tolls a b z,cost t q ≤ W+1 := by
  classical
  constructor
  · rintro ⟨N,J,line,z,j,r,par,cl,leaf,join⟩
    refine ⟨(N,J,line),⟨N,J,line,rfl,z,j,r,par,cl,fun p h=>(leaf p h).1,
      fun p h=>⟨(join p h).1,(join p h).2.1,(join p h).2.2.1⟩⟩,?_⟩
    apply (test_tolls t W a b N J line).mpr
    exact ⟨fun p h=>(leaf p h).2,fun p h=>(join p h).2.2.2⟩
  · rintro ⟨_,⟨N,J,line,rfl,z,j,r,par,cl,leaf,join⟩,h⟩
    obtain ⟨lh,jh⟩ := (test_tolls t W a b N J line).mp h
    exact ⟨N,J,line,z,j,r,par,cl,fun p h=>⟨leaf p h,lh p h⟩,fun p h=>
      ⟨(join p h).1,(join p h).2.1,(join p h).2.2,jh p h⟩⟩

theorem toll_cap {n : ℕ} (a b : Fin n→ℕ) (z : Tree n) :
    ∀ q∈tolls a b z,q.2 ≤ Finset.univ.sum b+1 := by
  classical
  have ub (A : Finset (Fin n)) : A.sum b ≤ Finset.univ.sum b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
  intro q h
  rcases Finset.mem_insert.mp h with eq|h
  · simp [eq]
  rcases Finset.mem_union.mp h with l|j
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp l
    exact Nat.add_le_add_right (ub _) 1
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp j
    exact (ub _).trans (Nat.le_add_right _ _)

theorem transfer_cost (B t : ℕ) (p q : ℕ×ℕ) (tp : B ≤ t) (pc : p.2 ≤ B) (qc : q.2 ≤ B)
    (h : cost (B+1) p ≤ cost (B+1) q) : cost t p ≤ cost t q := by
  dsimp only [cost] at *
  have slope : p.1 ≤ q.1 := by
    by_contra! big
    have x := Nat.mul_le_mul_left (B+1) (show q.1+1 ≤ p.1 by omega)
    rw [Nat.mul_succ] at x
    omega
  by_cases eq : p.1=q.1
  · simp only [eq] at *
    omega
  · have x := Nat.mul_le_mul_left t (show p.1+1 ≤ q.1 by omega)
    rw [Nat.mul_succ] at x
    omega

theorem stable {Z : Type*} (B : ℕ) (tags : Z→Finset (ℕ×ℕ)) (ok : Z→Prop)
    (non : ∃ z,ok z) (one : ∀ z,(0,1)∈tags z) (cap : ∀ z, ∀ q∈tags z,q.2 ≤ B) :
    ∃ z,ok z ∧ ∃ x∈tags z, ∀ t, B ≤ t →
      (1 ≤ cost t x) ∧ (∀ q∈tags z,cost t q ≤ cost t x) ∧
      ∀ y,ok y → ∃ v∈tags y,cost t x ≤ cost t v := by
  classical
  have best (z : Z) : ∃ x∈tags z,∀ q∈tags z,cost (B+1) q ≤ cost (B+1) x :=
    Finset.exists_max_image _ _ ⟨_,one z⟩
  let possible := fun k => ∃ z,ok z ∧ ∃ x∈tags z,cost (B+1) x=k ∧ ∀ q∈tags z,cost (B+1) q ≤ k
  have some : ∃ k,possible k := by
    obtain ⟨z,g⟩ := non
    obtain ⟨x,h,mx⟩ := best z
    exact ⟨cost (B+1) x,z,g,x,h,rfl,mx⟩
  obtain ⟨z,g,x,h,kx,bnd⟩ := Nat.find_spec some
  refine ⟨z,g,x,h,?_⟩
  intro t bt
  have up (q : ℕ×ℕ) (hq : q∈tags z) : cost t q ≤ cost t x :=
    transfer_cost B t q x bt (cap z q hq) (cap z x h) (kx ▸ bnd q hq)
  refine ⟨by simpa [cost] using up (0,1) (one z),up,?_⟩
  intro y gy
  obtain ⟨v,hv,mt⟩ := best y
  have bound := Nat.find_min' some (show possible (cost (B+1) v) from ⟨y,gy,v,hv,rfl,mt⟩)
  exact ⟨v,hv,transfer_cost B t x v bt (cap z x h) (cap y v hv) (kx ▸ bound)⟩

def canWin {n : ℕ} (w : Fin n→ℕ) (F : Set (Clause (Fin n))) (W : ℕ) :=
  ∃ π, IsRefutation (lifted w F) π ∧ ∀ C∈π,C.card ≤ W

theorem tree_test {n : ℕ} (w : Fin n→ℕ) (pos : ∀ i,0<w i) (F : Set (Clause (Fin n))) (W : ℕ) :
    canWin w F W ↔ T w F W ∅ := by
  constructor
  · rintro ⟨π,hπ,width⟩
    exact dir2 pos hπ width
  · exact dir1

theorem nonempty_lift {n : ℕ} (w : Fin n→ℕ) (F : Set (Clause (Fin n))) (h : ¬ Satisfiable F) :
    ∃ W,canWin w F W := by
  classical
  have hn : ¬Satisfiable (lifted w F) := by
    rintro ⟨x,sat⟩
    apply h
    refine ⟨par x,?_⟩
    intro C hC
    by_contra fail
    have f (l) (hl : l∈C) : par x l.1≠l.2 := fun eq=>fail ⟨l,hl,eq⟩
    obtain ⟨lit,hl,yes⟩ := sat _ (show rc (blk w (bv C)) x ∈ lifted w F from ⟨C,hC,x,f,rfl⟩)
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hl
    simpa using yes
  obtain ⟨π,hπ,_⟩ := completeness (lifted w F) hn
  exact ⟨Fintype.card (Raw w × Bool),π,hπ,fun C _=>Finset.card_le_univ C⟩

theorem affine_delta (t T : ℕ) (x : ℕ×ℕ) (lt : T ≤ t) (hp : 1 ≤ cost T x) :
    cost t x=(cost T x-1) + (t-T)*x.1 + 1 := by
  dsimp only [cost] at *
  have eq := Nat.sub_add_cancel lt
  have mul := congrArg (fun j=>j*x.1) (show t-T+T=t from eq)
  simp only [Nat.add_mul] at mul
  omega

end PEqualNP.Outside.L_pcx_313_aux

open PEqualNP.Outside.L_pcx_313_aux PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_313 : ∀ (n : ℕ) (slope offset : Fin n → ℕ), (∀ v, 0 < slope v + offset v) →
  let Base := PEqualNP.ProofComplexity.Clause (Fin n)
  let can := fun (a : Fin n → ℕ) (F : Set Base) (W : ℕ) =>
    let Raw := (v : Fin n) × Fin (a v)
    let val := fun (x : Raw → Bool) (v : Fin n) =>
      decide (Odd (((Finset.univ : Finset (Fin (a v))).filter (fun j => x ⟨v,j⟩ = true)).card))
    let lifted : Set (PEqualNP.ProofComplexity.Clause Raw) := {A |
      ∃ C ∈ F, ∃ x : Raw → Bool, (∀ l ∈ C, val x l.1 ≠ l.2) ∧
        A = ((Finset.univ : Finset Raw).filter (fun z => z.1 ∈ C.image Prod.fst)).image
          (fun z => (z, !(x z)))}
    ∃ π : List (PEqualNP.ProofComplexity.Clause Raw),
      PEqualNP.ProofComplexity.IsRefutation lifted π ∧ ∀ C ∈ π, C.card ≤ W
  let vars := fun (C : Base) => C.image Prod.fst
  let clean := fun (C : Base) => ∀ v, ¬ ((v,true) ∈ C ∧ (v,false) ∈ C)
  let w := fun (t : ℕ) (v : Fin n) => t * slope v + offset v
  let T := (Finset.univ : Finset (Fin n)).sum offset + 1
  ∀ F : Set Base, ¬ PEqualNP.ProofComplexity.Satisfiable F →
    ∃ (N J : Finset (List Bool)) (line : List Bool → Base) (d k : ℕ),
      [] ∈ N ∧ J ⊆ N ∧ line [] = ∅ ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      (∀ p ∈ N, clean (line p)) ∧ (∀ p ∈ N \ J, line p ∈ F) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N ∧
        PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) ∧
      ∀ t : ℕ, T ≤ t → ∀ W : ℕ,
        (can (w t) F W ↔ d + (t-T)*k ≤ W) ∧
        (can (w t) F W ↔
          (∀ p ∈ N \ J, (vars (line p)).sum (w t) ≤ W) ∧
          ∀ p ∈ J, (vars (line (p ++ [false])) ∪ vars (line (p ++ [true]))).sum (w t) ≤ W+1) := by
  classical
  intro n a b pos Base can vars clean w cutoff F hn
  have hp (t : ℕ) (large : cutoff ≤ t) : ∀ i,0<w t i := by
    intro i
    have bt : 1 ≤ cutoff := by dsimp only [cutoff]; omega
    have h := pos i
    change 0<t*a i+b i
    by_cases z : a i=0
    · simp [z] at h ⊢; exact h
    · have prod := Nat.mul_pos (by omega : 0<t) (by omega : 0<a i)
      omega
  have repr (t W : ℕ) (large : cutoff ≤ t) : can (w t) F W ↔
      ∃ z : Tree n,goodTree F z ∧ ∀ q∈tolls a b z,cost t q ≤ W+1 :=
    (tree_test (w t) (hp t large) F W).trans (smallTree t W a b F)
  obtain ⟨W,ok⟩ := nonempty_lift (w cutoff) F hn
  obtain ⟨z0,g0,_⟩ := (repr cutoff W le_rfl).mp ok
  obtain ⟨z,g,x,_,best⟩ := stable cutoff (tolls a b) (goodTree F) ⟨z0,g0⟩
    (fun z=>Finset.mem_insert_self _ _) (toll_cap a b)
  obtain ⟨N,J,line,rfl,root,sub,empty,parent,cln0,leaf,join⟩ := g
  refine ⟨N,J,line,cost cutoff x-1,x.1,root,sub,empty,parent,cln0,leaf,join,?_⟩
  have good : goodTree F (N,J,line) := ⟨N,J,line,rfl,root,sub,empty,parent,cln0,leaf,join⟩
  intro t large W
  obtain ⟨_,mx,mn⟩ := best t large
  have delta := affine_delta t cutoff x large (best cutoff le_rfl).1
  have ex : can (w t) F W ↔ cost t x ≤ W+1 := by
    rw [repr t W large]
    constructor
    · rintro ⟨y,gy,charges⟩
      obtain ⟨v,hv,lb⟩ := mn y gy
      exact lb.trans (charges v hv)
    · exact fun h=>⟨(N,J,line),good,fun q hq=>(mx q hq).trans h⟩
  refine ⟨ex.trans (by omega),?_⟩
  apply Iff.trans _ (test_tolls t W a b N J line)
  refine ex.trans ⟨fun h q hq=>(mx q hq).trans h,?_⟩
  intro all
  obtain ⟨v,hv,lb⟩ := mn (N,J,line) good
  exact lb.trans (all v hv)


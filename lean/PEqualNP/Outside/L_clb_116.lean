import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_845

namespace PEqualNP.Outside.L_clb_116_aux

section rect

variable {S p : ℕ}

def trc (lf rt : Fin p → Fin S → Fin S) : Fin S → List (Fin p) → List (Fin S)
  | _, [] => []
  | s, q :: Ps => lf q s :: rt q (lf q s) :: trc lf rt (rt q (lf q s)) Ps

def fin' (lf rt : Fin p → Fin S → Fin S) : Fin S → List (Fin p) → Fin S
  | s, [] => s
  | s, q :: Ps => fin' lf rt (rt q (lf q s)) Ps

theorem trc_length (lf rt : Fin p → Fin S → Fin S) (s : Fin S) (Ps : List (Fin p)) :
    (trc lf rt s Ps).length = 2 * Ps.length := by
  induction Ps generalizing s with
  | nil => rfl
  | cons q Ps ih => simp [trc, ih]; ring

theorem fin_eq (lf rt : Fin p → Fin S → Fin S) (s : Fin S) (Ps : List (Fin p)) :
    fin' lf rt s Ps = (trc lf rt s Ps).getLastD s := by
  induction Ps generalizing s with
  | nil => rfl
  | cons q Ps ih => simp only [fin', trc, List.getLastD_cons]; exact ih _

theorem rect (lf rt lf' rt' : Fin p → Fin S → Fin S) (Ps : List (Fin p)) (s : Fin S)
    (h : (trc lf rt s Ps).dropLast = (trc lf' rt' s Ps).dropLast) :
    trc lf rt' s Ps = trc lf' rt' s Ps := by
  induction Ps generalizing s with
  | nil => rfl
  | cons q Ps ih =>
    simp only [trc] at h ⊢
    rcases Ps with _ | ⟨q2, Ps'⟩
    · simp only [trc, List.dropLast_cons₂, List.dropLast_singleton] at h
      simp only [trc]
      obtain ⟨hu⟩ := List.cons_eq_cons.1 h
      rw [hu]
    · have hne : ∀ (l r : Fin p → Fin S → Fin S) (v : Fin S), trc l r v (q2 :: Ps') ≠ [] := by
        intro l r v; simp [trc]
      rw [List.dropLast_cons₂, List.dropLast_cons_of_ne_nil (hne _ _ _),
        List.dropLast_cons₂, List.dropLast_cons_of_ne_nil (hne _ _ _)] at h
      simp only [List.cons.injEq] at h
      obtain ⟨hu, hv, ht⟩ := h
      rw [hv] at ht
      rw [hu, ih _ ht]

theorem rect_fin (lf rt lf' rt' : Fin p → Fin S → Fin S) (Ps : List (Fin p)) (s : Fin S)
    (h : (trc lf rt s Ps).dropLast = (trc lf' rt' s Ps).dropLast) :
    fin' lf rt' s Ps = fin' lf' rt' s Ps := by
  rw [fin_eq, fin_eq, rect lf rt lf' rt' Ps s h]

end rect

theorem card_lists_le {S m : ℕ} (hS : 0 < S) (Λ : Finset (List (Fin S)))
    (hΛ : ∀ l ∈ Λ, l.length = m) : Λ.card ≤ S ^ m := by
  classical
  have : Λ.card ≤ (Finset.univ : Finset (Fin m → Fin S)).card := by
    refine Finset.card_le_card_of_injOn (fun l i => l.getD i ⟨0, hS⟩) (fun _ _ => by simp) ?_
    intro l hl l' hl' heq
    have h1 := hΛ l hl
    have h2 := hΛ l' hl'
    apply List.ext_getElem (by rw [h1, h2])
    intro i hi hi'
    have := congrFun heq ⟨i, by omega⟩
    dsimp only at this
    rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this
  simpa using this

theorem collision {α β : Type*} [DecidableEq α] [DecidableEq β] (D : Finset α) (τ : α → β)
    (T : ℕ) (hT : (D.image τ).card ≤ T) :
    D.card ^ 2 ≤ T * ((D ×ˢ D).filter (fun xy => τ xy.1 = τ xy.2)).card := by
  rw [Finset.card_eq_sum_card_image τ D]
  have hcs := sq_sum_le_card_mul_sum_sq (s := D.image τ)
    (f := fun b => (D.filter (fun a => τ a = b)).card)
  have hcol : ((D ×ˢ D).filter (fun xy => τ xy.1 = τ xy.2)).card =
      ∑ b ∈ D.image τ, (D.filter (fun a => τ a = b)).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun xy => τ xy.1) (t := D.image τ)
      (fun xy hxy => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy
        exact Finset.mem_image_of_mem τ hxy.1.1)]
    apply Finset.sum_congr rfl
    intro b _
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, he⟩, rfl⟩; exact ⟨⟨hx, rfl⟩, hy, he.symm⟩
    · rintro ⟨⟨hx, rfl⟩, hy, he⟩; exact ⟨⟨⟨hx, hy⟩, he.symm⟩, rfl⟩
  calc (∑ b ∈ D.image τ, (D.filter (fun a => τ a = b)).card) ^ 2
      ≤ (D.image τ).card * ∑ b ∈ D.image τ, (D.filter (fun a => τ a = b)).card ^ 2 := hcs
    _ ≤ T * _ := Nat.mul_le_mul_right _ hT
    _ = _ := by rw [hcol]

theorem pairs_le {ι : Type*} [DecidableEq ι] (D : Finset (Finset ι)) (P : Finset (Finset ι × Finset ι))
    (hP : P ⊆ D ×ˢ D) (hsymm : ∀ x y, (x, y) ∈ P → (y, x) ∈ P) :
    P.card ≤ D.card + 2 * (P.filter (fun xy => ¬ xy.1 ⊆ xy.2)).card := by
  have h1 : P.card = (P.filter (fun xy => xy.1 = xy.2)).card +
      (P.filter (fun xy => ¬ xy.1 ⊆ xy.2)).card +
      (P.filter (fun xy => xy.1 ⊆ xy.2 ∧ xy.1 ≠ xy.2)).card := by
    rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1; ext ⟨x, y⟩; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro h
        by_cases hxy : x ⊆ y
        · by_cases he : x = y
          · exact Or.inl (Or.inl ⟨h, he⟩)
          · exact Or.inr ⟨h, hxy, he⟩
        · exact Or.inl (Or.inr ⟨h, hxy⟩)
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    · rw [Finset.disjoint_left]; rintro ⟨x, y⟩ h1 h2
      simp only [Finset.mem_union, Finset.mem_filter] at h1 h2
      rcases h1 with ⟨_, he⟩ | ⟨_, hn⟩
      · exact h2.2.2 he
      · exact hn h2.2.1
    · rw [Finset.disjoint_left]; rintro ⟨x, y⟩ h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact h2.2 (h1.2 ▸ subset_refl _)
  have h2 : (P.filter (fun xy => xy.1 = xy.2)).card ≤ D.card := by
    refine Finset.card_le_card_of_injOn (fun xy => xy.1) (fun xy hxy => ?_) ?_
    · simp only [Finset.mem_coe, Finset.mem_filter] at hxy
      exact (Finset.mem_product.1 (hP hxy.1)).1
    · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' h
      simp only [Finset.mem_coe, Finset.mem_filter] at hxy hxy'
      simp only at h
      subst h
      rw [← hxy.2, ← hxy'.2]
  have h3 : (P.filter (fun xy => xy.1 ⊆ xy.2 ∧ xy.1 ≠ xy.2)).card ≤
      (P.filter (fun xy => ¬ xy.1 ⊆ xy.2)).card := by
    refine Finset.card_le_card_of_injOn (fun xy => (xy.2, xy.1)) (fun xy hxy => ?_) ?_
    · simp only [Finset.mem_coe, Finset.mem_filter] at hxy ⊢
      refine ⟨hsymm _ _ hxy.1, fun h => hxy.2.2 (Finset.Subset.antisymm hxy.2.1 h)⟩
    · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
  omega

theorem final_arith (A Q E R N T D F : ℕ) (hR : 0 < R) (hN : 0 < N)
    (h1 : A * R * N ≤ Q * D) (h2 : Q * F ≤ E * R * (N * (N - 1)))
    (h3 : D ^ 2 ≤ R * T * (D + 2 * F)) :
    A * (A * N - Q * T) ≤ 2 * E * Q * T * (N - 1) := by
  rcases le_or_gt (A * N) (Q * T) with hle | hlt
  · rw [Nat.sub_eq_zero_of_le hle, mul_zero]; exact Nat.zero_le _
  obtain ⟨N1, rfl⟩ : ∃ N1, N = N1 + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2 ⊢
  have hsub : ((A * (N1 + 1) - Q * T : ℕ) : ℤ) = (A : ℤ) * (N1 + 1) - Q * T := by
    rw [Nat.cast_sub hlt.le]; push_cast; ring
  zify at h1 h2 h3 hlt ⊢
  rw [hsub]
  set u : ℤ := Q * D
  set u0 : ℤ := A * R * (N1 + 1)
  set c : ℤ := R * T * Q
  have hu : u0 ≤ u := h1
  have hc : c < u0 := by
    have : (R : ℤ) * (Q * T) < R * (A * (N1 + 1)) := by
      apply mul_lt_mul_of_pos_left hlt; exact_mod_cast hR
    simp only [c, u0]; nlinarith
  have hQ3 : (Q : ℤ) ^ 2 * D ^ 2 ≤ Q ^ 2 * (R * T * (D + 2 * F)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have hF : (2 : ℤ) * R * T * Q * (Q * F) ≤ 2 * R * T * Q * (E * R * ((N1 + 1) * N1)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have key : u ^ 2 - c * u ≤ 2 * R * T * Q * (E * R * ((N1 + 1) * N1)) := by
    simp only [u, c]; nlinarith
  have hu0 : 0 ≤ u0 := by positivity
  have mono : u0 ^ 2 - c * u0 ≤ u ^ 2 - c * u := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (by linarith : (0:ℤ) ≤ u + u0 - c)]
  have hpos : (0 : ℤ) < R * R * (N1 + 1) := by positivity
  have : (R * R * (N1 + 1) : ℤ) * (A * ((A * (N1 + 1)) - Q * T)) ≤
      (R * R * (N1 + 1) : ℤ) * (2 * E * Q * T * N1) := by
    have e1 : u0 ^ 2 - c * u0 = (R * R * (N1 + 1) : ℤ) * (A * ((A * (N1 + 1)) - Q * T)) := by
      simp only [u0, c]; ring
    have e2 : 2 * R * T * Q * (E * R * ((N1 + 1) * N1)) =
        (R * R * (N1 + 1) : ℤ) * (2 * E * Q * T * N1) := by ring
    rw [← e1, ← e2]; linarith
  exact le_of_mul_le_mul_left this hpos

def runF {n p S : ℕ} {ρ : Type*} (st : Fin p → Fin n → Fin S → ρ → Fin S) (s0 : Fin S)
    (table : Fin n → ρ) : Fin S :=
  (List.finRange p).foldl (fun prev passId =>
    (List.finRange n).foldl (fun state site => st passId site state (table site)) prev) s0

theorem mem_take_lt {n a : ℕ} (site : Fin n) (h : site ∈ (List.finRange n).take a) : site.val < a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  simp only [List.getElem_take, List.getElem_finRange, Fin.cast_mk]
  simp at hi; omega

theorem mem_drop_ge {n a : ℕ} (site : Fin n) (h : site ∈ (List.finRange n).drop a) : a ≤ site.val := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  simp only [List.getElem_drop, List.getElem_finRange, Fin.cast_mk]
  omega

theorem run_split {n p S : ℕ} {ρ : Type*} (st : Fin p → Fin n → Fin S → ρ → Fin S) (s0 : Fin S)
    (a : ℕ) (tl tr table : Fin n → ρ) (htl : ∀ i, i.val < a → table i = tl i)
    (htr : ∀ i, a ≤ i.val → table i = tr i) :
    runF st s0 table = fin'
      (fun q s => ((List.finRange n).take a).foldl (fun state site => st q site state (tl site)) s)
      (fun q s => ((List.finRange n).drop a).foldl (fun state site => st q site state (tr site)) s)
      s0 (List.finRange p) := by
  unfold runF
  generalize List.finRange p = Ps
  induction Ps generalizing s0 with
  | nil => rfl
  | cons q Ps ih =>
    rw [List.foldl_cons, fin', ← ih]
    congr 1
    have hsplit : ∀ (f : Fin S → Fin n → Fin S) (s : Fin S), (List.finRange n).foldl f s =
        ((List.finRange n).drop a).foldl f (((List.finRange n).take a).foldl f s) := by
      intro f s
      conv_lhs => rw [← List.take_append_drop a (List.finRange n)]
      rw [List.foldl_append]
    have e1 : ((List.finRange n).take a).foldl (fun state site => st q site state (table site)) s0 =
        ((List.finRange n).take a).foldl (fun state site => st q site state (tl site)) s0 :=
      List.foldl_ext _ _ _ (fun st' site hs => by rw [htl site (mem_take_lt site hs)])
    have e2 : ∀ s, ((List.finRange n).drop a).foldl (fun state site => st q site state (table site)) s =
        ((List.finRange n).drop a).foldl (fun state site => st q site state (tr site)) s :=
      fun s => List.foldl_ext _ _ _ (fun st' site hs => by rw [htr site (mem_drop_ge site hs)])
    rw [hsplit, e1, e2]

theorem swap_count {R : ℕ} {α : Type*} (s : Finset α) (P : Fin R → α → Prop)
    [∀ c x, Decidable (P c x)] :
    ∑ c, (s.filter (P c)).card = ∑ x ∈ s, (Finset.univ.filter (fun c => P c x)).card := by
  simp only [Finset.card_filter]; exact Finset.sum_comm

theorem core (H n a p S R A E Q : ℕ) {ρ : Type*} (hp : 0 < p) (hR : 0 < R)
    (step : Fin R → Fin p → Fin n → Fin S → ρ → Fin S) (init : Fin R → Fin S)
    (empty : Fin R → Fin S → Bool)
    (tl tr : Finset (Fin H) → Fin n → ρ) (tab : Finset (Fin H) → Finset (Fin H) → Fin n → ρ)
    (htl : ∀ X Y i, i.val < a → tab X Y i = tl X i) (htr : ∀ X Y i, a ≤ i.val → tab X Y i = tr Y i)
    (hc : ∀ X, A * R ≤ Q * (Finset.univ.filter
      (fun c => empty c (runF (step c) (init c) (tab X X)) = true)).card)
    (hs : ∀ X Y, ¬ X ⊆ Y → Q * (Finset.univ.filter
      (fun c => empty c (runF (step c) (init c) (tab X Y)) = true)).card ≤ E * R) :
    A * (A * 2 ^ H - Q * S ^ (2 * p - 1)) ≤ 2 * E * Q * S ^ (2 * p - 1) * (2 ^ H - 1) := by
  classical
  have hS : 0 < S := Fin.pos (init ⟨0, hR⟩)
  set T := S ^ (2 * p - 1) with hT
  set U := (Finset.univ : Finset (Finset (Fin H))) with hU
  have hN : U.card = 2 ^ H := by simp [U]
  let lf := fun (c : Fin R) (X : Finset (Fin H)) (q : Fin p) (s : Fin S) =>
    ((List.finRange n).take a).foldl (fun state site => step c q site state (tl X site)) s
  let rt := fun (c : Fin R) (Y : Finset (Fin H)) (q : Fin p) (s : Fin S) =>
    ((List.finRange n).drop a).foldl (fun state site => step c q site state (tr Y site)) s
  have hrun : ∀ c X Y, runF (step c) (init c) (tab X Y) =
      fin' (lf c X) (rt c Y) (init c) (List.finRange p) :=
    fun c X Y => run_split (step c) (init c) a (tl X) (tr Y) (tab X Y) (htl X Y) (htr X Y)
  let acc := fun (c : Fin R) (X Y : Finset (Fin H)) =>
    empty c (runF (step c) (init c) (tab X Y)) = true
  let τ := fun (c : Fin R) (X : Finset (Fin H)) =>
    (trc (lf c X) (rt c X) (init c) (List.finRange p)).dropLast
  have hcross : ∀ c X Y, τ c X = τ c Y → acc c Y Y → acc c X Y := by
    intro c X Y h hY
    show empty c _ = true
    rw [hrun, rect_fin (lf c X) (rt c X) (lf c Y) (rt c Y) _ _ h, ← hrun]
    exact hY
  have hτlen : ∀ c X, (τ c X).length = 2 * p - 1 := by
    intro c X; simp [τ, trc_length]
  let Dc := fun c => U.filter (fun X => acc c X X)
  let Fc := fun c => (U ×ˢ U).filter (fun xy => ¬ xy.1 ⊆ xy.2 ∧ acc c xy.1 xy.2)
  have hcoin : ∀ c, (Dc c).card ^ 2 ≤ T * ((Dc c).card + 2 * (Fc c).card) := by
    intro c
    set P := ((Dc c) ×ˢ (Dc c)).filter (fun xy => τ c xy.1 = τ c xy.2) with hP
    have h1 := collision (Dc c) (τ c) T (card_lists_le hS _ (fun l hl => by
      obtain ⟨X, _, rfl⟩ := Finset.mem_image.1 hl; exact hτlen c X))
    have h2 := pairs_le (Dc c) P (Finset.filter_subset _ _) (fun x y hxy => by
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hxy ⊢
      exact ⟨⟨hxy.1.2, hxy.1.1⟩, hxy.2.symm⟩)
    have h3 : (P.filter (fun xy => ¬ xy.1 ⊆ xy.2)).card ≤ (Fc c).card := by
      apply Finset.card_le_card
      intro ⟨X, Y⟩ hxy
      simp only [hP, Dc, Fc, Finset.mem_filter, Finset.mem_product] at hxy ⊢
      exact ⟨⟨Finset.mem_univ _, Finset.mem_univ _⟩, hxy.2, hcross c X Y hxy.1.2 hxy.1.1.2.2⟩
    calc (Dc c).card ^ 2 ≤ T * P.card := h1
      _ ≤ T * ((Dc c).card + 2 * (Fc c).card) := Nat.mul_le_mul_left _ (by omega)
  set Dsum := ∑ c, (Dc c).card
  set Fsum := ∑ c, (Fc c).card
  have h3 : Dsum ^ 2 ≤ R * T * (Dsum + 2 * Fsum) := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin R)))
      (f := fun c => (Dc c).card)
    rw [Finset.card_univ, Fintype.card_fin] at this
    calc Dsum ^ 2 ≤ R * ∑ c, (Dc c).card ^ 2 := this
      _ ≤ R * ∑ c, T * ((Dc c).card + 2 * (Fc c).card) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun c _ => hcoin c))
      _ = R * T * (Dsum + 2 * Fsum) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have h1 : A * R * 2 ^ H ≤ Q * Dsum := by
    have e : Dsum = ∑ X ∈ U, (Finset.univ.filter (fun c => acc c X X)).card :=
      swap_count U (fun c X => acc c X X)
    rw [e, Finset.mul_sum, ← hN, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun X _ => hc X)
  have h2 : Q * Fsum ≤ E * R * (2 ^ H * (2 ^ H - 1)) := by
    set G := (U ×ˢ U).filter (fun xy => ¬ xy.1 ⊆ xy.2)
    have e : Fsum = ∑ xy ∈ G, (Finset.univ.filter (fun c => acc c xy.1 xy.2)).card := by
      rw [← swap_count G (fun c xy => acc c xy.1 xy.2)]
      apply Finset.sum_congr rfl; intro c _
      simp only [Fc, G, Finset.filter_filter]
    have hG : G.card ≤ 2 ^ H * (2 ^ H - 1) := by
      have : G ⊆ U.offDiag := by
        intro ⟨X, Y⟩ h
        simp only [G, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag] at h ⊢
        exact ⟨h.1.1, h.1.2, fun e => h.2 (e ▸ subset_refl _)⟩
      calc G.card ≤ U.offDiag.card := Finset.card_le_card this
        _ = 2 ^ H * (2 ^ H - 1) := by rw [Finset.offDiag_card, hN, Nat.mul_sub_one]
    rw [e, Finset.mul_sum]
    calc ∑ xy ∈ G, Q * (Finset.univ.filter (fun c => acc c xy.1 xy.2)).card
        ≤ ∑ xy ∈ G, E * R := Finset.sum_le_sum (fun xy hxy => by
          simp only [G, Finset.mem_filter] at hxy; exact hs xy.1 xy.2 hxy.2)
      _ = G.card * (E * R) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (2 ^ H * (2 ^ H - 1)) * (E * R) := Nat.mul_le_mul_right _ hG
      _ = E * R * (2 ^ H * (2 ^ H - 1)) := by ring
  exact final_arith A Q E R (2 ^ H) T Dsum Fsum hR (by positivity) h1 h2 h3

theorem pow_big (m : ℕ) (hm : 6 ≤ m) : 4 * m + 10 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem params (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a + 1) (h32 : 32 ≤ a + b) :
    2 * b ≤ 2 ^ Nat.clog 2 (2 * b) ∧ 5 ≤ Nat.clog 2 (2 * b) ∧ 2 * Nat.clog 2 (2 * b) + 3 ≤ a ∧
      2 ^ (Nat.clog 2 (2 * b) - 3) ≤ a - Nat.clog 2 (2 * b) - 1 := by
  set c := Nat.clog 2 (2 * b) with hc
  have h1 : 2 * b ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have ha : 16 ≤ a := by omega
  have h2 : 2 * c + 3 ≤ a := by
    have hm : c ≤ (a - 3) / 2 := by
      rw [hc, Nat.clog_le_iff_le_pow (by norm_num)]
      have := pow_big ((a - 3) / 2) (by omega)
      omega
    omega
  have h5 : 5 ≤ c := by
    by_contra hlt
    have : 2 ^ c ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 2 ^ (c - 1) < 2 * b := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (x := 2 * b) (by omega)
    rwa [← hc, Nat.pred_eq_sub_one] at this
  have h4 : 2 ^ (c - 1) = 2 ^ (c - 3) * 4 := by
    rw [show c - 1 = (c - 3) + 2 by omega, pow_add]; norm_num
  refine ⟨h1, h5, h2, ?_⟩
  omega

theorem M_bound (a b h c M : ℕ) (hab : a ≤ b) (hh : h ≤ c) (h5 : 5 ≤ c) (h2 : 2 * c + 3 ≤ a)
    (h3 : 2 ^ (c - 3) ≤ a - c - 1)
    (hM : (a - h - 1) * 2 ^ (a - c - 3) * ((b - h - 1) * 2 ^ (b - c - 3)) ≤ M) :
    2 ^ (a + b - 13) ≤ M := by
  have ea : 2 ^ (c - 3) ≤ a - h - 1 := le_trans h3 (by omega)
  have eb : 2 ^ (c - 3) ≤ b - h - 1 := le_trans h3 (by omega)
  calc 2 ^ (a + b - 13) ≤ 2 ^ ((c - 3) + (a - c - 3) + ((c - 3) + (b - c - 3))) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (c - 3) * 2 ^ (a - c - 3) * (2 ^ (c - 3) * 2 ^ (b - c - 3)) := by
        rw [pow_add, pow_add, pow_add]
    _ ≤ (a - h - 1) * 2 ^ (a - c - 3) * ((b - h - 1) * 2 ^ (b - c - 3)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ ea) (Nat.mul_le_mul_right _ eb)
    _ ≤ M := hM

theorem len_filter {R : ℕ} (P : Fin R → Bool) :
    ((List.finRange R).filter P).length = (Finset.univ.filter (fun c => P c = true)).card := by
  rw [Fin.univ_def]
  simp [Finset.card, Finset.filter_val]

end PEqualNP.Outside.L_clb_116_aux

theorem PEqualNP.Outside.L_clb_116 : (∀ (n w p : Nat) (hn : 0 < n), 32 ≤ n → 0 < p →
  n-(w+1) ≤ Nat.clog 2 (2*(n-n/2)) →
  let Pat := Fin (w+1) → Bool
  let Row := Pat → Bool
  let Tab := Fin n → Row
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let total := fun (table : Tab) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      ∀ i : Fin n, table i (fun j => x (loc (i.val+j.val))) = true)).card
  let run := fun (S : Nat) (start : Fin S)
      (step : Fin p → Fin n → Fin S → Row → Fin S) (table : Tab) =>
    (List.finRange p).foldl (fun prev passId =>
      (List.finRange n).foldl (fun state site => step passId site state (table site)) prev) start
  let H := 2^(n-13)
  let N := 2^H
  ∀ (S R A E Q : Nat), 0 < R → 0 < Q → A ≤ Q → E ≤ Q →
    ∀ (init : Fin R → Fin S) (update : Fin R → Fin p → Fin n → Fin S → Row → Fin S)
      (empty : Fin R → Fin S → Bool),
      let declares := fun input : Tab => ((List.finRange R).filter (fun coin =>
        empty coin (run S (init coin) (update coin) input))).length
      let T := S^(2*p-1)
      (∀ table : Tab, total table = 0 → A*R ≤ Q*declares table) →
      (∀ table : Tab, 0 < total table → Q*declares table ≤ E*R) →
      A*(A*N-Q*T) ≤ 2*E*Q*T*(N-1)) := by
  intro n w p hn h32 hp hcl
  obtain ⟨a, b, rfl, hab, hba⟩ : ∃ a b, n = a + b ∧ a ≤ b ∧ b ≤ a + 1 :=
    ⟨n / 2, n - n / 2, by omega, by omega, by omega⟩
  have hb2 : a + b - (a + b) / 2 = b := by omega
  rw [hb2] at hcl
  obtain ⟨hc1, hc5, hc2, hc3⟩ := PEqualNP.Outside.L_clb_116_aux.params a b hab hba h32
  obtain ⟨M, code, base, left, right, hM, hcode, hleft, hright, hlr, hsol⟩ :=
    PEqualNP.Outside.L_lib_845 a b w (Nat.clog 2 (2 * b)) hn hcl
      (by rw [min_eq_left hab]; omega) (by rw [max_eq_right hab]; exact hc1)
  intro Pat Row Tab loc total run H N S R A E Q hR hQ hAQ hEQ init update empty declares T hcomp hsound
  have hHM : H ≤ M := PEqualNP.Outside.L_clb_116_aux.M_bound a b _ _ M hab hcl hc5 hc2 hc3 hM
  let ι : Fin H ↪ Fin M := Fin.castLEEmb hHM
  let tab : Finset (Fin H) → Finset (Fin H) → Tab := fun X Y i pat =>
    base (i, pat) || decide ((i, pat) ∈ (X.map ι).image left) ||
      decide ((i, pat) ∈ ((Finset.univ \ Y).map ι).image right)
  let tl : Finset (Fin H) → Tab := fun X i pat =>
    base (i, pat) || decide ((i, pat) ∈ (X.map ι).image left)
  let tr : Finset (Fin H) → Tab := fun Y i pat =>
    base (i, pat) || decide ((i, pat) ∈ ((Finset.univ \ Y).map ι).image right)
  have htl : ∀ X Y i, i.val < a → tab X Y i = tl X i := by
    intro X Y i hi; funext pat
    have : (i, pat) ∉ ((Finset.univ \ Y).map ι).image right := by
      intro hm; obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hm
      have := (hlr k).2.1; rw [hk] at this; dsimp only at this; omega
    simp only [tab, tl, this, decide_false, Bool.or_false]
  have htr : ∀ X Y i, a ≤ i.val → tab X Y i = tr Y i := by
    intro X Y i hi; funext pat
    have : (i, pat) ∉ (X.map ι).image left := by
      intro hm; obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hm
      have := (hlr k).1; rw [hk] at this; dsimp only at this; omega
    simp only [tab, tr, this, decide_false, Bool.or_false]
  have htot : ∀ X Y, total (tab X Y) = (X \ Y).card := by
    intro X Y
    refine (congrArg Finset.card (hsol (X.map ι) ((Finset.univ \ Y).map ι))).trans ?_
    rw [Finset.card_image_of_injective _ hcode, ← Finset.map_inter, Finset.card_map]
    congr 1; ext x; simp
  have hdecl : ∀ X Y, declares (tab X Y) = (Finset.univ.filter
      (fun c => empty c (PEqualNP.Outside.L_clb_116_aux.runF (update c) (init c) (tab X Y)) = true)).card :=
    fun X Y => PEqualNP.Outside.L_clb_116_aux.len_filter _
  exact PEqualNP.Outside.L_clb_116_aux.core H (a + b) a p S R A E Q hp hR update init empty tl tr tab
    htl htr
    (fun X => by
      rw [← hdecl]; exact hcomp _ (by rw [htot]; simp))
    (fun X Y hXY => by
      rw [← hdecl]; exact hsound _ (by rw [htot]; exact Finset.card_pos.2 (Finset.sdiff_nonempty.2 hXY)))

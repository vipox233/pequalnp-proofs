import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_955_aux

def Aff {V : Type} [AddCommGroup V] (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x - y + z ∈ S

theorem aff_filter {V : Type} [AddCommGroup V] [DecidableEq V] {S : Finset V} (hS : Aff S)
    (φ : V → ZMod 2) (hφ : ∀ x y z, φ (x - y + z) = φ x - φ y + φ z)
    (Q : ZMod 2 → Prop) [DecidablePred Q] (hQ : ∀ u v, Q u → Q v → u = v) :
    Aff (S.filter (fun x => Q (φ x))) := by
  intro x hx y hy z hz
  simp only [Finset.mem_filter] at hx hy hz ⊢
  refine ⟨hS x hx.1 y hy.1 z hz.1, ?_⟩
  rw [hφ, hQ _ _ hy.2 hx.2, hQ _ _ hz.2 hx.2]
  simpa using hx.2

theorem dot_aff {n : ℕ} (w : Fin n → ZMod 2) (x y z : Fin n → ZMod 2) :
    dotProduct w (x - y + z) = dotProduct w x - dotProduct w y + dotProduct w z := by
  rw [dotProduct_add, dotProduct_sub]

theorem z3 : ∀ a b c : ZMod 2, a ≠ c → b ≠ c → a = b := by decide

theorem card_half {n : ℕ} {S : Finset (Fin n → ZMod 2)} (hS : Aff S) (w : Fin n → ZMod 2)
    (x1 : Fin n → ZMod 2) (hx1 : x1 ∈ S) :
    S.card ≤ 2 * (S.filter (fun y => dotProduct w y = dotProduct w x1)).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := S) (fun y => dotProduct w y = dotProduct w x1)
  have h1 : (S.filter (fun y => ¬ dotProduct w y = dotProduct w x1)).card ≤
      (S.filter (fun y => dotProduct w y = dotProduct w x1)).card := by
    by_cases hne : (S.filter (fun y => ¬ dotProduct w y = dotProduct w x1)).Nonempty
    · obtain ⟨z, hz⟩ := hne
      rw [Finset.mem_filter] at hz
      refine Finset.card_le_card_of_injOn (fun y => y - z + x1) ?_ ?_
      · intro y hy
        rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
        refine ⟨hS y hy.1 z hz.1 x1 hx1, ?_⟩
        rw [dot_aff, z3 _ _ _ hy.2 hz.2]
        ring
      · intro y _ y' _ hyy
        simpa using hyy
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  omega

def errs {n m : ℕ} (a b P : Fin m → Fin n → ZMod 2) (d : Fin m → ZMod 2) (y : Fin n → ZMod 2) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i => dotProduct (a i) y * dotProduct (b i) y ≠ dotProduct (P i) y + d i)

theorem z6 : ∀ c By Py Bx Px d : ZMod 2, c * By + Py = c * Bx + Px → c * Bx ≠ Px + d →
    ¬ (c * By ≠ Py + (d + 1)) := by decide

theorem z6b : ∀ c By Py Bx Px d : ZMod 2, c * By + Py = c * Bx + Px → c * Bx ≠ Px + d →
    c * By ≠ Py + d := by decide

theorem step1 {n m : ℕ} (a b P : Fin m → Fin n → ZMod 2) (d : Fin m → ZMod 2)
    {B : Finset (Fin n → ZMod 2)} (hB : Aff B) (x1 : Fin n → ZMod 2) (hx1 : x1 ∈ B) (i : Fin m)
    (hi : i ∈ errs a b P d x1) :
    ∃ B' : Finset (Fin n → ZMod 2), B' ⊆ B ∧ Aff B' ∧ x1 ∈ B' ∧ B.card ≤ 4 * B'.card ∧
      ∀ y ∈ B', errs a b P (Function.update d i (d i + 1)) y = (errs a b P d y).erase i ∧
        i ∈ errs a b P d y := by
  classical
  set c := dotProduct (a i) x1
  set w := c • b i + P i
  let B1 := B.filter (fun y => dotProduct (a i) y = c)
  let B2 := B1.filter (fun y => dotProduct w y = dotProduct w x1)
  have hB1 : Aff B1 := aff_filter hB _ (dot_aff _) (fun u => u = c) (fun u v hu hv => hu.trans hv.symm)
  have hB2 : Aff B2 := aff_filter hB1 _ (dot_aff _) (fun u => u = dotProduct w x1)
    (fun u v hu hv => hu.trans hv.symm)
  have hx11 : x1 ∈ B1 := Finset.mem_filter.2 ⟨hx1, rfl⟩
  have hx12 : x1 ∈ B2 := Finset.mem_filter.2 ⟨hx11, rfl⟩
  have c1 : B.card ≤ 2 * B1.card := card_half hB (a i) x1 hx1
  have c2 : B1.card ≤ 2 * B2.card := card_half hB1 w x1 hx11
  have hi' : c * dotProduct (b i) x1 ≠ dotProduct (P i) x1 + d i := by
    simpa [errs] using hi
  have key : ∀ y ∈ B2, ¬ (dotProduct (a i) y * dotProduct (b i) y ≠
      dotProduct (P i) y + (d i + 1)) ∧
      dotProduct (a i) y * dotProduct (b i) y ≠ dotProduct (P i) y + d i := by
    intro y hy
    simp only [B2, B1, Finset.mem_filter] at hy
    obtain ⟨⟨_, hya⟩, hyw⟩ := hy
    have hw : ∀ z, dotProduct w z = c * dotProduct (b i) z + dotProduct (P i) z := by
      intro z; simp [w, add_dotProduct, smul_dotProduct]
    rw [hw, hw] at hyw
    rw [hya]
    exact ⟨z6 _ _ _ _ _ _ hyw hi', z6b _ _ _ _ _ _ hyw hi'⟩
  refine ⟨B2, fun y hy => (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).1, hB2, hx12, by omega,
    fun y hy => ⟨?_, ?_⟩⟩
  · ext j
    simp only [errs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, ne_eq, not_true_eq_false, false_and, iff_false]
      exact (key y hy).1
    · rw [Function.update_of_ne hj]
      tauto
  · simpa [errs] using (key y hy).2

theorem reduce {n m : ℕ} (a b P : Fin m → Fin n → ZMod 2) (f : ℕ) : ∀ (k : ℕ)
    (B : Finset (Fin n → ZMod 2)) (d : Fin m → ZMod 2), Aff B → B.Nonempty →
    (∀ y ∈ B, (errs a b P d y).card ≤ f + k) →
    ∃ (B' : Finset (Fin n → ZMod 2)) (d' : Fin m → ZMod 2), Aff B' ∧ B'.Nonempty ∧
      B.card ≤ 4 ^ k * B'.card ∧ ∀ y ∈ B', (errs a b P d' y).card ≤ f := by
  classical
  intro k
  induction k with
  | zero => intro B d hB hne h; exact ⟨B, d, hB, hne, by simp, h⟩
  | succ k ih =>
    intro B d hB hne h
    by_cases hex : ∃ y ∈ B, ∃ i, i ∈ errs a b P d y
    · obtain ⟨x1, hx1, i, hi⟩ := hex
      obtain ⟨B2, _, hB2, hx12, hc, hy⟩ := step1 a b P d hB x1 hx1 i hi
      obtain ⟨B', d', hB', hne', hc', h'⟩ := ih B2 (Function.update d i (d i + 1)) hB2 ⟨x1, hx12⟩
        (by
          intro y hyB
          obtain ⟨e1, e2⟩ := hy y hyB
          rw [e1, Finset.card_erase_of_mem e2]
          have := h y (by
            obtain ⟨B2s, _⟩ := step1 a b P d hB x1 hx1 i hi
            exact (‹B2 ⊆ B› hyB))
          omega)
      exact ⟨B', d', hB', hne', by rw [pow_succ]; nlinarith, h'⟩
    · push Not at hex
      refine ⟨B, d, hB, hne, by nlinarith [Nat.one_le_pow (k+1) 4 (by norm_num)], ?_⟩
      intro y hy
      have : errs a b P d y = ∅ := Finset.eq_empty_of_forall_notMem (hex y hy)
      simp [this]

theorem foldl_iter {α β : Type} (g : α → α) : ∀ (l : List β) (q : α),
    l.foldl (fun p _ => g p) q = g^[l.length] q := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons x l ih => intro q; simp only [List.foldl_cons, List.length_cons]; rw [ih]; rfl

def stp {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Fin n → ZMod 2)
    (bias : List Bool → ZMod 2) (x : Fin n → ZMod 2) : List Bool → List Bool :=
  fun p => if p ∈ T then p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)] else p

theorem zbit : ∀ (u v β : ZMod 2) (bb : Bool), decide (u + β ≠ 0) = bb →
    decide (v + β ≠ 0) = bb → u = v := by decide

theorem desc_disj (q r : List Bool) (h0 : q ++ [false] <+: r) (h1 : q ++ [true] <+: r) : False := by
  rw [List.prefix_iff_eq_take] at h0 h1
  have : q ++ [false] = q ++ [true] := by
    rw [h0, h1]; simp
  simp at this

theorem leaf {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Fin n → ZMod 2)
    (bias : List Bool → ZMod 2) : ∀ (k : ℕ) (q : List Bool) (S : Finset (Fin n → ZMod 2)),
    Aff S → ∃ (p : List Bool) (S' : Finset (Fin n → ZMod 2)), S' ⊆ S ∧ Aff S' ∧
      (∀ x ∈ S', (stp T ask bias x)^[k] q = p) ∧
      S.card ≤ ((T.filter (fun r => q <+: r)).card + 1) * S'.card := by
  classical
  intro k
  induction k with
  | zero =>
    intro q S hS
    exact ⟨q, S, subset_rfl, hS, fun x _ => rfl, by nlinarith⟩
  | succ k ih =>
    intro q S hS
    by_cases hq : q ∈ T
    · let bitf : (Fin n → ZMod 2) → Bool := fun x => decide (dotProduct (ask q) x + bias q ≠ 0)
      have hSb : ∀ bb : Bool, Aff (S.filter (fun x => bitf x = bb)) := by
        intro bb
        exact aff_filter hS (fun x => dotProduct (ask q) x) (dot_aff _)
          (fun u => decide (u + bias q ≠ 0) = bb) (fun u v hu hv => zbit u v _ bb hu hv)
      obtain ⟨p0, S0, hS0, hA0, hr0, hc0⟩ := ih (q ++ [false]) _ (hSb false)
      obtain ⟨p1, S1, hS1, hA1, hr1, hc1⟩ := ih (q ++ [true]) _ (hSb true)
      have hrun : ∀ bb : Bool, ∀ x ∈ S.filter (fun x => bitf x = bb),
          (stp T ask bias x)^[k+1] q = (stp T ask bias x)^[k] (q ++ [bb]) := by
        intro bb x hx
        rw [Finset.mem_filter] at hx
        rw [Function.iterate_succ_apply]
        congr 1
        simp only [stp, hq, if_true]
        rw [← hx.2]
      have hsplit : S.card = (S.filter (fun x => bitf x = false)).card +
          (S.filter (fun x => bitf x = true)).card := by
        rw [← Finset.card_filter_add_card_filter_not (s := S) (fun x => bitf x = false)]
        congr 2
        ext x; simp
      have hcnt : (T.filter (fun r => (q ++ [false]) <+: r)).card +
          (T.filter (fun r => (q ++ [true]) <+: r)).card + 1 ≤
          (T.filter (fun r => q <+: r)).card := by
        have hsub : insert q ((T.filter (fun r => (q ++ [false]) <+: r)) ∪
            (T.filter (fun r => (q ++ [true]) <+: r))) ⊆ T.filter (fun r => q <+: r) := by
          intro r hr
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hr ⊢
          rcases hr with rfl | ⟨hr, h⟩ | ⟨hr, h⟩
          · exact ⟨hq, List.prefix_refl _⟩
          · exact ⟨hr, (List.prefix_append _ _).trans h⟩
          · exact ⟨hr, (List.prefix_append _ _).trans h⟩
        have hnot : q ∉ (T.filter (fun r => (q ++ [false]) <+: r)) ∪
            (T.filter (fun r => (q ++ [true]) <+: r)) := by
          simp only [Finset.mem_union, Finset.mem_filter]
          rintro (⟨_, h⟩ | ⟨_, h⟩) <;> simpa using h.length_le
        have hdisj : Disjoint (T.filter (fun r => (q ++ [false]) <+: r))
            (T.filter (fun r => (q ++ [true]) <+: r)) := by
          rw [Finset.disjoint_left]
          intro r h0 h1
          exact desc_disj q r (Finset.mem_filter.1 h0).2 (Finset.mem_filter.1 h1).2
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj] at this
        exact this
      by_cases hm : S1.card ≤ S0.card
      · refine ⟨p0, S0, hS0.trans (Finset.filter_subset _ _), hA0, ?_, ?_⟩
        · intro x hx
          rw [hrun false x (hS0 hx)]; exact hr0 x hx
        · nlinarith
      · refine ⟨p1, S1, hS1.trans (Finset.filter_subset _ _), hA1, ?_, ?_⟩
        · intro x hx
          rw [hrun true x (hS1 hx)]; exact hr1 x hx
        · nlinarith
    · obtain ⟨p, S', h1, h2, h3, h4⟩ := ih q S hS
      refine ⟨p, S', h1, h2, ?_, h4⟩
      intro x hx
      rw [Function.iterate_succ_apply]
      have : stp T ask bias x q = q := by simp [stp, hq]
      rw [this]; exact h3 x hx

theorem kadd {n : ℕ} {B : Finset (Fin n → ZMod 2)} (hB : Aff B) {x0 : Fin n → ZMod 2}
    (hx0 : x0 ∈ B) {u v : Fin n → ZMod 2} (hu : x0 + u ∈ B) (hv : x0 + v ∈ B) :
    x0 + (u + v) ∈ B := by
  have := hB _ hu _ hx0 _ hv
  convert this using 1; abel

theorem ksmul {n : ℕ} {B : Finset (Fin n → ZMod 2)} {x0 : Fin n → ZMod 2}
    (hx0 : x0 ∈ B) (c : ZMod 2) {v : Fin n → ZMod 2} (hv : x0 + v ∈ B) :
    x0 + c • v ∈ B := by
  have zc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases zc c with rfl | rfl
  · simpa using hx0
  · simpa using hv

def Kmod {n : ℕ} (B : Finset (Fin n → ZMod 2)) (hB : Aff B) (x0 : Fin n → ZMod 2) (hx0 : x0 ∈ B) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {v | x0 + v ∈ B}, zero_mem' := by simpa using hx0, add_mem' := fun hu hv => kadd hB hx0 hu hv,
    smul_mem' := fun c _ hv => ksmul hx0 c hv }

theorem shift_iff {n : ℕ} (a b P x δ : Fin n → ZMod 2) (d : ZMod 2) :
    (dotProduct a x * dotProduct b x ≠
      dotProduct (P - dotProduct b δ • a - dotProduct a δ • b) x +
        (dotProduct P δ + d - dotProduct a δ * dotProduct b δ)) ↔
    (dotProduct a (x + δ) * dotProduct b (x + δ) ≠ dotProduct P (x + δ) + d) := by
  rw [← sub_ne_zero, ← sub_ne_zero (a := dotProduct a (x + δ) * _)]
  have : dotProduct a x * dotProduct b x -
      (dotProduct (P - dotProduct b δ • a - dotProduct a δ • b) x +
        (dotProduct P δ + d - dotProduct a δ * dotProduct b δ)) =
      dotProduct a (x + δ) * dotProduct b (x + δ) - (dotProduct P (x + δ) + d) := by
    simp only [dotProduct_add, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [this]

theorem flat {n m f : ℕ} (a b P : Fin m → Fin n → ZMod 2) (d : Fin m → ZMod 2)
    (B : Finset (Fin n → ZMod 2)) (hB : Aff B) (x0 : Fin n → ZMod 2) (hx0 : x0 ∈ B)
    (herr : ∀ y ∈ B, (errs a b P d y).card ≤ f) :
    ∃ (h : ℕ) (ask : Fin h → Fin n → ZMod 2) (P' : (Fin h → ZMod 2) → Fin m → Fin n → ZMod 2)
      (d' : (Fin h → ZMod 2) → Fin m → ZMod 2), 2 ^ h * B.card = 2 ^ n ∧ ∀ x : Fin n → ZMod 2,
      (Finset.univ.filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠
        dotProduct (P' (fun j => dotProduct (ask j) x) i) x +
          d' (fun j => dotProduct (ask j) x) i)).card ≤ f := by
  classical
  let K := Kmod B hB x0 hx0
  let Q := (Fin n → ZMod 2) ⧸ K
  let hh := Module.finrank (ZMod 2) Q
  let E := (Module.finBasis (ZMod 2) Q).equivFun
  let R : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin hh → ZMod 2) := E.toLinearMap ∘ₗ K.mkQ
  let ask : Fin hh → Fin n → ZMod 2 := fun j => LinearMap.toMatrix' R j
  have hask : ∀ x, (fun j => dotProduct (ask j) x) = R x := by
    intro x
    rw [← LinearMap.toMatrix'_mulVec R x]
    rfl
  let rep : (Fin hh → ZMod 2) → (Fin n → ZMod 2) := fun p =>
    Classical.choose (K.mkQ_surjective (E.symm p))
  have hrep : ∀ p, K.mkQ (rep p) = E.symm p := fun p =>
    Classical.choose_spec (K.mkQ_surjective (E.symm p))
  let δ : (Fin hh → ZMod 2) → Fin n → ZMod 2 := fun p => x0 - rep p
  refine ⟨hh, ask, fun p i => P i - dotProduct (b i) (δ p) • a i - dotProduct (a i) (δ p) • b i,
    fun p i => dotProduct (P i) (δ p) + d i - dotProduct (a i) (δ p) * dotProduct (b i) (δ p),
    ?_, ?_⟩
  · have h1 := K.card_eq_card_quotient_mul_card
    have h2 : Nat.card K = B.card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.addLeft x0) (fun v => Iff.rfl))
    have h3 : Nat.card Q = 2 ^ hh := by
      rw [Nat.card_congr E.toEquiv]; simp; rfl
    have h4 : Nat.card (Fin n → ZMod 2) = 2 ^ n := by simp
    rw [h2, h3, h4] at h1
    rw [h1]; ring
  · intro x
    rw [hask x]
    have hmem : x + δ (R x) ∈ B := by
      have : x - rep (R x) ∈ K := by
        have e1 : K.mkQ x = K.mkQ (rep (R x)) := by
          rw [hrep]; apply E.injective; simp [R] <;> rfl
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.eq] using e1
      have h' : x0 + (x - rep (R x)) ∈ B := this
      convert h' using 1
      simp only [δ]; abel
    refine le_trans (le_of_eq ?_) (herr _ hmem)
    unfold errs
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact shift_iff _ _ _ _ _ _

theorem tree_flat {n m L e f : ℕ} (a b : Fin m → Fin n → ZMod 2) (hfe : f ≤ e)
    (T : Finset (List Bool)) (ask : List Bool → Fin n → ZMod 2) (bias : List Bool → ZMod 2)
    (P : List Bool → Fin m → Fin n → ZMod 2) (bb : List Bool → Fin m → ZMod 2) (hT : T.card < L)
    (hx : ∀ x, (errs a b (P ((stp T ask bias x)^[T.card] [])) (bb ((stp T ask bias x)^[T.card] [])) x).card ≤ e) :
    ∃ (B : Finset (Fin n → ZMod 2)) (P0 : Fin m → Fin n → ZMod 2) (d : Fin m → ZMod 2),
      Aff B ∧ B.Nonempty ∧ 2 ^ n ≤ L * 4 ^ (e - f) * B.card ∧ ∀ y ∈ B, (errs a b P0 d y).card ≤ f := by
  classical
  obtain ⟨p, S', -, hA, hrun, hc⟩ := leaf T ask bias T.card [] Finset.univ
    (fun _ _ _ _ _ _ => Finset.mem_univ _)
  have hcT : (T.filter (fun r => [] <+: r)).card = T.card := by
    rw [Finset.filter_true_of_mem (fun r _ => List.nil_prefix)]
  rw [hcT, Finset.card_univ] at hc
  have hcard : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp
  rw [hcard] at hc
  have hne : S'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h] at hc; simp at hc
  obtain ⟨B, d, hB, hBne, hBc, herrB⟩ := reduce a b (P p) f (e - f) S' (bb p) hA hne (by
    intro y hy
    have := hx y
    rw [hrun y hy] at this
    omega)
  refine ⟨B, P p, d, hB, hBne, ?_, herrB⟩
  calc 2 ^ n ≤ (T.card + 1) * S'.card := hc
    _ ≤ L * (4 ^ (e - f) * B.card) := Nat.mul_le_mul (by omega) hBc
    _ = _ := by ring

theorem run_eq {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Fin n → ZMod 2)
    (bias : List Bool → ZMod 2) (x : Fin n → ZMod 2) :
    (List.range T.card).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)] else p) [] =
    (stp T ask bias x)^[T.card] [] := by
  have := foldl_iter (stp T ask bias x) (List.range T.card) []
  rw [List.length_range] at this
  exact this

theorem part1 (n m e f L : Nat) (a b : Fin m → (Fin n → ZMod 2)) (hfe : f ≤ e)
    (T : Finset (List Bool)) (ask : List Bool → Fin n → ZMod 2) (bias : List Bool → ZMod 2)
    (P : List Bool → Fin m → Fin n → ZMod 2) (bb : List Bool → Fin m → ZMod 2) (hT : T.card < L)
    (hx : ∀ x, (errs a b (P ((stp T ask bias x)^[T.card] [])) (bb ((stp T ask bias x)^[T.card] [])) x).card ≤ e) :
    ∃ (h : Nat) (ask : Fin h → (Fin n → ZMod 2)) (P : (Fin h → ZMod 2) → Fin m → (Fin n → ZMod 2))
      (d : (Fin h → ZMod 2) → Fin m → ZMod 2),
      2^h ≤ 4^(e-f)*L ∧ ∀ x : Fin n → ZMod 2,
      ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠
        dotProduct (P (fun j => dotProduct (ask j) x) i) x + d (fun j => dotProduct (ask j) x) i)).card ≤ f := by
  obtain ⟨B, P0, d, hB, ⟨x0, hx0⟩, hc, herr⟩ := tree_flat a b hfe T ask bias P bb hT hx
  obtain ⟨h, ask', P', d', hh, hx'⟩ := flat a b P0 d B hB x0 hx0 herr
  refine ⟨h, ask', P', d', ?_, hx'⟩
  have hpos : 0 < B.card := Finset.card_pos.2 ⟨x0, hx0⟩
  have : 2 ^ h * B.card ≤ (4 ^ (e - f) * L) * B.card := by rw [hh]; linarith
  exact Nat.le_of_mul_le_mul_right this hpos

def tg (g : ℕ) (x : Fin (3*g) → ZMod 2) (i : Fin (4*g)) : ZMod 2 :=
  let bit := fun j : Nat => (List.ofFn x).getD (3*(i.val/4)+j) 0
  let u := bit 0
  let v := bit 1
  let w := bit 2
  if i.val % 4 = 0 then u*v else if i.val % 4 = 1 then u*w
    else if i.val % 4 = 2 then v*w else (u+v)*(u+w)

def E {N : ℕ} (k : ℕ) : Fin N → ZMod 2 := fun c => if c.val = k then 1 else 0

theorem dotE {N : ℕ} (k : ℕ) (x : Fin N → ZMod 2) :
    dotProduct (E k) x = (List.ofFn x).getD k 0 := by
  by_cases hk : k < N
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [dotProduct, E]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp [hk]
    · intro c _ hc
      have : c.val ≠ k := fun h => hc (Fin.ext h)
      simp [this]
    · simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp only [dotProduct, E]
    apply Finset.sum_eq_zero
    intro c _
    have : c.val ≠ k := by omega
    simp [this]

theorem dotE' {N : ℕ} (k : ℕ) (hk : k < N) (x : Fin N → ZMod 2) :
    dotProduct (E k) x = x ⟨k, hk⟩ := by
  rw [dotE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hk]

def Av (g : ℕ) (i : Fin (4*g)) : Fin (3*g) → ZMod 2 :=
  if i.val % 4 = 0 then E (3*(i.val/4)) else if i.val % 4 = 1 then E (3*(i.val/4))
    else if i.val % 4 = 2 then E (3*(i.val/4)+1) else E (3*(i.val/4)) + E (3*(i.val/4)+1)

def Bv (g : ℕ) (i : Fin (4*g)) : Fin (3*g) → ZMod 2 :=
  if i.val % 4 = 0 then E (3*(i.val/4)+1) else if i.val % 4 = 1 then E (3*(i.val/4)+2)
    else if i.val % 4 = 2 then E (3*(i.val/4)+2) else E (3*(i.val/4)) + E (3*(i.val/4)+2)

theorem tg_prod (g : ℕ) (x : Fin (3*g) → ZMod 2) (i : Fin (4*g)) :
    tg g x i = dotProduct (Av g i) x * dotProduct (Bv g i) x := by
  unfold tg Av Bv
  split_ifs <;> simp [add_dotProduct, dotE]

theorem blk : ∀ u1 v1 w1 u2 v2 w2 u3 v3 w3 : ZMod 2,
    (u1 - u2 + u3) * (v1 - v2 + v3) = u1 * v1 - u2 * v2 + u3 * v3 →
    (u1 - u2 + u3) * (w1 - w2 + w3) = u1 * w1 - u2 * w2 + u3 * w3 →
    (v1 - v2 + v3) * (w1 - w2 + w3) = v1 * w1 - v2 * w2 + v3 * w3 →
    (u1 = u2 ∧ v1 = v2 ∧ w1 = w2) ∨ (u2 = u3 ∧ v2 = v3 ∧ w2 = w3) ∨ (u1 = u3 ∧ v1 = v3 ∧ w1 = w3) := by
  set_option synthInstance.maxSize 2000 in
  set_option synthInstance.maxHeartbeats 400000 in
  decide

theorem card_le_two {X : Type} [DecidableEq X] (S : Finset X)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a = b ∨ b = c ∨ a = c) : S.card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hc
  rcases h a ha b hb c hc' with h1 | h1 | h1
  · exact hab h1
  · exact hbc h1
  · exact hac h1

def Phi (g : ℕ) (x : Fin (3*g) → ZMod 2) : Fin g → Fin 3 → ZMod 2 :=
  fun j k => x ⟨3 * j.val + k.val, by omega⟩

theorem phi_inj (g : ℕ) : Function.Injective (Phi g) := by
  intro x y h
  funext c
  have hc : 3 * (c.val / 3) + c.val % 3 = c.val := Nat.div_add_mod _ _
  have := congrFun (congrFun h ⟨c.val / 3, by omega⟩) ⟨c.val % 3, by omega⟩
  simp only [Phi] at this
  have e : (⟨3 * (c.val / 3) + c.val % 3, by omega⟩ : Fin (3*g)) = c := Fin.ext hc
  rwa [e] at this

theorem flat_card (g : ℕ) (B : Finset (Fin (3*g) → ZMod 2)) (hB : Aff B)
    (P0 : Fin (4*g) → Fin (3*g) → ZMod 2) (d : Fin (4*g) → ZMod 2)
    (hex : ∀ y ∈ B, ∀ i, tg g y i = dotProduct (P0 i) y + d i) : B.card ≤ 2 ^ g := by
  classical
  have hadd : ∀ y1 ∈ B, ∀ y2 ∈ B, ∀ y3 ∈ B, ∀ i,
      tg g (y1 - y2 + y3) i = tg g y1 i - tg g y2 i + tg g y3 i := by
    intro y1 h1 y2 h2 y3 h3 i
    rw [hex _ (hB _ h1 _ h2 _ h3), hex _ h1, hex _ h2, hex _ h3, dot_aff]
    ring
  have hval : ∀ y : Fin (3*g) → ZMod 2, ∀ j : Fin g, ∀ r : ℕ, (hr : r < 3) →
      tg g y ⟨4 * j.val + r, by omega⟩ =
        if r = 0 then Phi g y j 0 * Phi g y j 1 else if r = 1 then Phi g y j 0 * Phi g y j 2
          else Phi g y j 1 * Phi g y j 2 := by
    intro y j r hr
    have h1 : (4 * j.val + r) / 4 = j.val := by omega
    have h2 : (4 * j.val + r) % 4 = r := by omega
    unfold tg
    simp only [h1, h2]
    rw [← dotE, ← dotE, ← dotE, dotE' _ (by omega), dotE' _ (by omega), dotE' _ (by omega)]
    interval_cases r <;> simp [Phi]
  let S := B.image (Phi g)
  have hS : ∀ j : Fin g, (S.image (fun z => z j)).card ≤ 2 := by
    intro j
    apply card_le_two
    intro a ha b hb c hc
    simp only [S, Finset.mem_image] at ha hb hc
    obtain ⟨_, ⟨y1, h1, rfl⟩, rfl⟩ := ha
    obtain ⟨_, ⟨y2, h2, rfl⟩, rfl⟩ := hb
    obtain ⟨_, ⟨y3, h3, rfl⟩, rfl⟩ := hc
    have e0 := hadd y1 h1 y2 h2 y3 h3 ⟨4 * j.val + 0, by omega⟩
    have e1 := hadd y1 h1 y2 h2 y3 h3 ⟨4 * j.val + 1, by omega⟩
    have e2 := hadd y1 h1 y2 h2 y3 h3 ⟨4 * j.val + 2, by omega⟩
    rw [hval _ j 0 (by omega), hval _ j 0 (by omega), hval _ j 0 (by omega),
      hval _ j 0 (by omega)] at e0
    rw [hval _ j 1 (by omega), hval _ j 1 (by omega), hval _ j 1 (by omega),
      hval _ j 1 (by omega)] at e1
    rw [hval _ j 2 (by omega), hval _ j 2 (by omega), hval _ j 2 (by omega),
      hval _ j 2 (by omega)] at e2
    simp only [if_true, show (1:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 0 by omega,
      show (2:ℕ) ≠ 1 by omega, if_false] at e0 e1 e2
    have hp : ∀ k, Phi g (y1 - y2 + y3) j k = Phi g y1 j k - Phi g y2 j k + Phi g y3 j k := by
      intro k; rfl
    rw [hp, hp] at e0 e1 e2
    have fe : ∀ z z' : Fin 3 → ZMod 2, z 0 = z' 0 → z 1 = z' 1 → z 2 = z' 2 → z = z' := by
      intro z z' a0 a1 a2; funext k; fin_cases k <;> assumption
    rcases blk _ _ _ _ _ _ _ _ _ e0 e1 e2 with ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩
    · exact Or.inl (fe _ _ a0 a1 a2)
    · exact Or.inr (Or.inl (fe _ _ a0 a1 a2))
    · exact Or.inr (Or.inr (fe _ _ a0 a1 a2))
  have hsub : S ⊆ Fintype.piFinset (fun j => S.image (fun z => z j)) := by
    intro z hz
    exact Fintype.mem_piFinset.2 (fun j => Finset.mem_image_of_mem _ hz)
  calc B.card = S.card := (Finset.card_image_of_injective _ (phi_inj g)).symm
    _ ≤ (Fintype.piFinset (fun j => S.image (fun z => z j))).card := Finset.card_le_card hsub
    _ = ∏ j, (S.image (fun z => z j)).card := Fintype.card_piFinset _
    _ ≤ 2 ^ (Finset.univ : Finset (Fin g)).card :=
        Finset.prod_le_pow_card _ _ _ (fun j _ => hS j)
    _ = 2 ^ g := by simp

theorem part2_fwd (g t L : ℕ) (T : Finset (List Bool)) (ask : List Bool → Fin (3*g) → ZMod 2)
    (bias : List Bool → ZMod 2) (P : List Bool → Fin (4*g) → Fin (3*g) → ZMod 2)
    (bb : List Bool → Fin (4*g) → ZMod 2) (hT : T.card < L)
    (hx : ∀ x, ((Finset.univ : Finset (Fin (4*g))).filter (fun i => tg g x i ≠
      dotProduct (P ((stp T ask bias x)^[T.card] []) i) x + bb ((stp T ask bias x)^[T.card] []) i)).card ≤ t) :
    4 ^ (g - t) ≤ L := by
  classical
  have hx' : ∀ x, (errs (Av g) (Bv g) (P ((stp T ask bias x)^[T.card] []))
      (bb ((stp T ask bias x)^[T.card] [])) x).card ≤ t := by
    intro x
    refine le_trans (le_of_eq ?_) (hx x)
    unfold errs
    congr 1
    ext i
    simp [tg_prod]
  obtain ⟨B, P0, d, hB, ⟨x0, hx0⟩, hc, herr⟩ :=
    tree_flat (f := 0) (Av g) (Bv g) (Nat.zero_le t) T ask bias P bb hT hx'
  have hex : ∀ y ∈ B, ∀ i, tg g y i = dotProduct (P0 i) y + d i := by
    intro y hy i
    have h0 := herr y hy
    rw [Nat.le_zero, Finset.card_eq_zero] at h0
    by_contra hne
    have : i ∈ errs (Av g) (Bv g) P0 d y := by
      simp only [errs, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← tg_prod]
    rw [h0] at this; simp at this
  have hB2 := flat_card g B hB P0 d hex
  rw [Nat.sub_zero] at hc
  by_cases htg : g ≤ t
  · rw [Nat.sub_eq_zero_of_le htg]; simp; omega
  · have e1 : 2 ^ (3 * g) = 4 ^ g * 2 ^ g := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; ring_nf
    have e2 : 4 ^ g = 4 ^ (g - t) * 4 ^ t := by rw [← pow_add]; congr 1; omega
    have h1 : 4 ^ (g - t) * 4 ^ t * 2 ^ g ≤ L * 4 ^ t * 2 ^ g := by
      calc 4 ^ (g - t) * 4 ^ t * 2 ^ g = 2 ^ (3 * g) := by rw [e1, e2]
        _ ≤ L * 4 ^ t * B.card := hc
        _ ≤ L * 4 ^ t * 2 ^ g := Nat.mul_le_mul_left _ hB2
    have h2 : 0 < 4 ^ t * 2 ^ g := by positivity
    have : 4 ^ (g - t) * (4 ^ t * 2 ^ g) ≤ L * (4 ^ t * 2 ^ g) := by
      simpa [mul_assoc] using h1
    exact Nat.le_of_mul_le_mul_right this h2

def cid (j : ℕ) : ℕ := 3 * (j / 2) + j % 2

def Tset (s : ℕ) : Finset (List Bool) :=
  (Finset.range (2 * s)).biUnion (fun k => (Finset.univ : Finset (Fin k → Bool)).image List.ofFn)

theorem memT (s : ℕ) (p : List Bool) : p ∈ Tset s ↔ p.length < 2 * s := by
  simp only [Tset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨k, hk, f, rfl⟩; simpa using hk
  · intro h; exact ⟨p.length, h, p.get, List.ofFn_get p⟩

theorem geom : ∀ N : ℕ, (∑ k ∈ Finset.range N, 2 ^ k) + 1 = 2 ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem cardT_lt (s : ℕ) : (Tset s).card < 4 ^ s := by
  have h1 : (Tset s).card ≤ ∑ k ∈ Finset.range (2 * s), 2 ^ k := by
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun k _ => ?_))
    refine Finset.card_image_le.trans ?_
    simp
  have h2 := geom (2 * s)
  have h3 : (4:ℕ) ^ s = 2 ^ (2 * s) := by rw [pow_mul]; norm_num
  omega

theorem cardT_ge (s : ℕ) : 2 * s ≤ (Tset s).card := by
  have hsub : (Finset.range (2 * s)).image (fun k => List.replicate k false) ⊆ Tset s := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [memT]; simpa using hk
  have hinj : Function.Injective (fun k => List.replicate k false) := by
    intro a b h; simpa using congrArg List.length h
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at this
  exact this

def askF (g : ℕ) (p : List Bool) : Fin (3 * g) → ZMod 2 := E (cid p.length)

def st {N : ℕ} (x : Fin N → ZMod 2) (k : ℕ) : List Bool :=
  (List.range k).map (fun j => decide (dotProduct (E (cid j)) x ≠ 0))

theorem iter_st (g s : ℕ) (x : Fin (3 * g) → ZMod 2) : ∀ k ≤ 2 * s,
    (stp (Tset s) (askF g) (fun _ => 0) x)^[k] [] = st x k := by
  intro k
  induction k with
  | zero => intro _; simp [st]
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hl : (st x k).length = k := by simp [st]
    have hm : st x k ∈ Tset s := by rw [memT, hl]; omega
    simp only [stp, hm, if_true, askF, hl, add_zero]
    simp [st, List.range_succ]

theorem run_st (g s : ℕ) (x : Fin (3 * g) → ZMod 2) :
    (stp (Tset s) (askF g) (fun _ => 0) x)^[(Tset s).card] [] = st x (2 * s) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (cardT_ge s)
  rw [hr, add_comm, Function.iterate_add_apply, iter_st g s x _ le_rfl]
  apply Function.iterate_fixed
  have hl : (st x (2 * s)).length = 2 * s := by simp [st]
  have hm : st x (2 * s) ∉ Tset s := by rw [memT, hl]; omega
  simp [stp, hm]

def rd (p : List Bool) (k : ℕ) : ZMod 2 := if p.getD k false = true then 1 else 0

theorem zdec : ∀ z : ZMod 2, (if decide (z ≠ 0) = true then (1 : ZMod 2) else 0) = z := by decide

theorem rd_st {N : ℕ} (x : Fin N → ZMod 2) (M k : ℕ) (hk : k < M) :
    rd (st x M) k = dotProduct (E (cid k)) x := by
  unfold rd st
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  exact zdec _

def tv (u v w : ZMod 2) (r : ℕ) : ZMod 2 :=
  if r = 0 then u*v else if r = 1 then u*w else if r = 2 then v*w else (u+v)*(u+w)

def pv (fx : Bool) (u v w : ZMod 2) (r : ℕ) : ZMod 2 :=
  if fx then (if r = 0 then u*v else if r = 1 then u*w else if r = 2 then v*w
    else (u+v)*w + (u+v)*u)
  else (if r = 0 then 0 else if r = 1 then w else if r = 2 then v+w+1 else u+v)

theorem lemC : ∀ r, r < 4 → ∀ u v w : ZMod 2, tv u v w r = pv true u v w r := by
  intro r hr
  interval_cases r <;> decide

theorem lemD : ∀ r r', r < 4 → r' < 4 → ∀ u v w : ZMod 2, tv u v w r ≠ pv false u v w r →
    tv u v w r' ≠ pv false u v w r' → r = r' := by
  intro r r' hr hr'
  interval_cases r <;> interval_cases r' <;> decide

def Pp (g s : ℕ) (p : List Bool) (i : Fin (4 * g)) : Fin (3 * g) → ZMod 2 :=
  if i.val / 4 < s then
    (if i.val % 4 = 0 then 0 else if i.val % 4 = 1 then rd p (2 * (i.val / 4)) • E (3 * (i.val / 4) + 2)
      else if i.val % 4 = 2 then rd p (2 * (i.val / 4) + 1) • E (3 * (i.val / 4) + 2)
      else (rd p (2 * (i.val / 4)) + rd p (2 * (i.val / 4) + 1)) • E (3 * (i.val / 4) + 2))
  else (if i.val % 4 = 0 then 0 else if i.val % 4 = 1 then E (3 * (i.val / 4) + 2)
      else if i.val % 4 = 2 then E (3 * (i.val / 4) + 1) + E (3 * (i.val / 4) + 2)
      else E (3 * (i.val / 4)) + E (3 * (i.val / 4) + 1))

def bp (g s : ℕ) (p : List Bool) (i : Fin (4 * g)) : ZMod 2 :=
  if i.val / 4 < s then
    (if i.val % 4 = 0 then rd p (2 * (i.val / 4)) * rd p (2 * (i.val / 4) + 1)
      else if i.val % 4 = 1 then 0 else if i.val % 4 = 2 then 0
      else (rd p (2 * (i.val / 4)) + rd p (2 * (i.val / 4) + 1)) * rd p (2 * (i.val / 4)))
  else (if i.val % 4 = 0 then 0 else if i.val % 4 = 1 then 0 else if i.val % 4 = 2 then 1 else 0)

def gd {N : ℕ} (x : Fin N → ZMod 2) (k : ℕ) : ZMod 2 := (List.ofFn x).getD k 0

theorem tg_tv (g : ℕ) (x : Fin (3 * g) → ZMod 2) (i : Fin (4 * g)) :
    tg g x i = tv (gd x (3 * (i.val / 4))) (gd x (3 * (i.val / 4) + 1)) (gd x (3 * (i.val / 4) + 2))
      (i.val % 4) := by
  unfold tg tv gd
  simp only [add_zero]

theorem pred_pv (g s : ℕ) (x : Fin (3 * g) → ZMod 2) (i : Fin (4 * g)) :
    dotProduct (Pp g s (st x (2 * s)) i) x + bp g s (st x (2 * s)) i =
      pv (decide (i.val / 4 < s)) (gd x (3 * (i.val / 4))) (gd x (3 * (i.val / 4) + 1))
        (gd x (3 * (i.val / 4) + 2)) (i.val % 4) := by
  unfold Pp bp pv
  by_cases hj : i.val / 4 < s
  · have hU : rd (st x (2 * s)) (2 * (i.val / 4)) = gd x (3 * (i.val / 4)) := by
      rw [rd_st x _ _ (by omega), dotE]
      unfold gd cid; congr 2; omega
    have hV : rd (st x (2 * s)) (2 * (i.val / 4) + 1) = gd x (3 * (i.val / 4) + 1) := by
      rw [rd_st x _ _ (by omega), show cid (2 * (i.val / 4) + 1) = 3 * (i.val / 4) + 1 by
        unfold cid; omega, dotE]
      rfl
    simp only [hj, if_true, decide_true, hU, hV]
    split_ifs <;> simp [smul_dotProduct, dotE, gd] <;> ring
  · simp only [hj, if_false, decide_false, Bool.false_eq_true]
    split_ifs <;> simp [add_dotProduct, dotE, gd]

theorem part2_back (g t L : ℕ) (hL : 4 ^ (g - t) ≤ L) :
    ∃ (T : Finset (List Bool)) (ask : List Bool → Fin (3 * g) → ZMod 2) (bias : List Bool → ZMod 2)
      (P : List Bool → Fin (4 * g) → Fin (3 * g) → ZMod 2) (b : List Bool → Fin (4 * g) → ZMod 2),
      T.card < L ∧ ∀ x, ((Finset.univ : Finset (Fin (4 * g))).filter (fun i => tg g x i ≠
        dotProduct (P ((stp T ask bias x)^[T.card] []) i) x + b ((stp T ask bias x)^[T.card] []) i)).card ≤ t := by
  classical
  let s := g - t
  refine ⟨Tset s, askF g, fun _ => 0, Pp g s, bp g s, lt_of_lt_of_le (cardT_lt s) hL, ?_⟩
  intro x
  rw [run_st]
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin (4 * g))).filter (fun i => tg g x i ≠
      dotProduct (Pp g s (st x (2 * s)) i) x + bp g s (st x (2 * s)) i),
      s ≤ i.val / 4 ∧ tv (gd x (3 * (i.val / 4))) (gd x (3 * (i.val / 4) + 1))
        (gd x (3 * (i.val / 4) + 2)) (i.val % 4) ≠ pv false (gd x (3 * (i.val / 4)))
        (gd x (3 * (i.val / 4) + 1)) (gd x (3 * (i.val / 4) + 2)) (i.val % 4) := by
    intro i hi
    rw [Finset.mem_filter, tg_tv, pred_pv] at hi
    by_cases hj : i.val / 4 < s
    · exfalso
      rw [decide_eq_true hj] at hi
      exact hi.2 (lemC _ (Nat.mod_lt _ (by norm_num)) _ _ _)
    · rw [decide_eq_false hj] at hi
      exact ⟨by omega, hi.2⟩
  calc _ ≤ (Finset.Ico s g).card := by
        refine Finset.card_le_card_of_injOn (fun i => i.val / 4) ?_ ?_
        · intro i hi
          have := (hmaps i hi).1
          have hi4 := i.isLt
          simp only [Finset.coe_Ico, Set.mem_Ico]
          omega
        · intro i hi i' hi' hii
          have h1 := (hmaps i hi).2
          have h2 := (hmaps i' hi').2
          simp only at hii
          rw [hii] at h1
          have := lemD _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) _ _ _ h1 h2
          apply Fin.ext
          have e1 := Nat.div_add_mod i.val 4
          have e2 := Nat.div_add_mod i'.val 4
          omega
    _ = g - s := Nat.card_Ico _ _
    _ ≤ t := by omega

end PEqualNP.Outside.L_lib_955_aux

theorem PEqualNP.Outside.L_lib_955 : (let F := ZMod 2
let H := List Bool
let feasible := fun (n m L err : Nat) (target : (Fin n → F) → Fin m → F) =>
  let W := Fin n → F
  let run := fun (T : Finset H) (ask : H → W) (bias : H → F) (x : W) =>
    (List.range T.card).foldl (fun (p : H) _ =>
      if p ∈ T then p ++ [decide (dotProduct (ask p) x+bias p ≠ 0)] else p) []
  ∃ (T : Finset H) (ask : H → W) (bias : H → F) (P : H → Fin m → W) (b : H → Fin m → F),
    T.card < L ∧ ∀ x : W,
      let p := run T ask bias x
      ((Finset.univ : Finset (Fin m)).filter (fun i => target x i ≠ dotProduct (P p i) x+b p i)).card ≤ err
(∀ (n m e f L : Nat) (a b : Fin m → (Fin n → F)), f ≤ e →
  let target := fun (x : Fin n → F) (i : Fin m) => dotProduct (a i) x*dotProduct (b i) x
  feasible n m L e target →
  ∃ (h : Nat) (ask : Fin h → (Fin n → F)) (P : (Fin h → F) → Fin m → (Fin n → F))
      (d : (Fin h → F) → Fin m → F),
    2^h ≤ 4^(e-f)*L ∧ ∀ x : Fin n → F,
      let p := fun j => dotProduct (ask j) x
      ((Finset.univ : Finset (Fin m)).filter (fun i => target x i ≠ dotProduct (P p i) x+d p i)).card ≤ f) ∧
(∀ (g t L : Nat),
  let target := fun (x : Fin (3*g) → F) (i : Fin (4*g)) =>
    let bit := fun j : Nat => (List.ofFn x).getD (3*(i.val/4)+j) 0
    let u := bit 0
    let v := bit 1
    let w := bit 2
    if i.val % 4 = 0 then u*v else if i.val % 4 = 1 then u*w
      else if i.val % 4 = 2 then v*w else (u+v)*(u+w)
  feasible (3*g) (4*g) L t target ↔ 4^(g-t) ≤ L)) := by
  intro F H feasible
  refine ⟨?_, ?_⟩
  · intro n m e f L a b hfe target hfeas
    obtain ⟨T, ask, bias, P, bb, hT, hx⟩ := hfeas
    refine PEqualNP.Outside.L_lib_955_aux.part1 n m e f L a b hfe T ask bias P bb hT ?_
    intro x
    have := hx x
    simp only [] at this
    rw [PEqualNP.Outside.L_lib_955_aux.run_eq] at this
    exact this
  · intro g t L target
    constructor
    · rintro ⟨T, ask, bias, P, bb, hT, hx⟩
      refine PEqualNP.Outside.L_lib_955_aux.part2_fwd g t L T ask bias P bb hT (fun x => ?_)
      have := hx x
      simp only [] at this
      rw [PEqualNP.Outside.L_lib_955_aux.run_eq] at this
      exact this
    · intro hL
      obtain ⟨T, ask, bias, P, bb, hT, hx⟩ := PEqualNP.Outside.L_lib_955_aux.part2_back g t L hL
      refine ⟨T, ask, bias, P, bb, hT, fun x => ?_⟩
      simp only []
      rw [PEqualNP.Outside.L_lib_955_aux.run_eq]
      exact hx x

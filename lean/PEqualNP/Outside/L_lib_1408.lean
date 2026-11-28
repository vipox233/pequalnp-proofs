import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1408

theorem gen {r m : Nat} (W : Fin m → Finset (Fin r)) (X : Finset (Fin r))
    (Q : Fin m → Finset (Fin r) → Prop)
    (hQ : ∀ i A B, A ⊆ B → B ⊆ W i → Q i A → Q i B) :
    ((∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ Q i (Y i)) ↔
      ∀ i, Q i (X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t))) ∧
    ((∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ Q i (Y i)) →
      ((∀ i j, i ≤ j → X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) ⊆
          X.filter (fun k => ∀ t : Fin m, j ≤ t → k ∈ W t)) ∧
        ∀ i, X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) ⊆ X ∧
          X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) ⊆ W i ∧
          Q i (X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t))) ∧
      ∀ Y : Fin m → Finset (Fin r), ((∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ Q i (Y i)) →
        ∀ i, Y i ⊆ X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t)) := by
  have hmono : ∀ i j : Fin m, i ≤ j → X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) ⊆
          X.filter (fun k => ∀ t : Fin m, j ≤ t → k ∈ W t) := by
    intro i j hij k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, fun t ht => hk.2 t (le_trans hij ht)⟩
  have hX : ∀ i : Fin m, X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) ⊆ X :=
    fun i => Finset.filter_subset _ _
  have hW : ∀ i : Fin m, X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) ⊆ W i := by
    intro i k hk
    simp only [Finset.mem_filter] at hk
    exact hk.2 i le_rfl
  have hmax : ∀ Y : Fin m → Finset (Fin r), ((∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ Q i (Y i)) →
        ∀ i, Y i ⊆ X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t) := by
    rintro Y ⟨h1, h2⟩ i k hk
    simp only [Finset.mem_filter]
    exact ⟨(h2 i).1 hk, fun t ht => (h2 t).2.1 (h1 i t ht hk)⟩
  have hiff : (∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ Q i (Y i)) ↔
      ∀ i, Q i (X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t)) := by
    constructor
    · rintro ⟨Y, hY⟩ i
      exact hQ i _ _ (hmax Y hY i) (hW i) (hY.2 i).2.2
    · intro h
      exact ⟨_, hmono, fun i => ⟨hX i, hW i, h i⟩⟩
  refine ⟨hiff, fun h => ⟨⟨hmono, fun i => ⟨hX i, hW i, hiff.1 h i⟩⟩, hmax⟩⟩

theorem key {r m : Nat} (W : Fin m → Finset (Fin r)) (X : Finset (Fin r)) (e : Nat) :
    (∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ (W i \ Y i).card ≤ e) ↔
      ∀ i, (W i \ X.filter (fun k => ∀ t : Fin m, i ≤ t → k ∈ W t)).card ≤ e :=
  (gen W X (fun i A => (W i \ A).card ≤ e) (fun i A B hAB _ h =>
    le_trans (Finset.card_le_card (Finset.sdiff_subset_sdiff (le_refl _) hAB)) h)).1


theorem sub {r m e : Nat} (W : Fin m → Finset (Fin r)) (X : Finset (Fin r)) :
    (∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ (W i \ Y i).card ≤ e) ↔
      ∀ k : Nat, k ≤ e+2 → ∀ f : Fin k → Fin m, StrictMono f →
        ∃ Y : Fin k → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
          ∀ i, Y i ⊆ X ∧ Y i ⊆ (W ∘ f) i ∧ ((W ∘ f) i \ Y i).card ≤ e := by
  constructor
  · rintro ⟨Y, h1, h2⟩ k _ f hf
    exact ⟨Y ∘ f, fun i j hij => h1 _ _ (hf.monotone hij), fun i => h2 (f i)⟩
  · intro h
    rw [key]
    by_contra hne
    simp only [not_forall, not_le] at hne
    obtain ⟨i, hi⟩ := hne
    obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hi)
    have hg : ∀ x ∈ S, x ∈ X → ∃ t : Fin m, i ≤ t ∧ x ∉ W t := by
      intro x hx hxX
      have := hS hx
      simp only [Finset.mem_sdiff, Finset.mem_filter, not_and, not_forall] at this
      obtain ⟨_, h3⟩ := this
      obtain ⟨t, ht, ht2⟩ := h3 hxX
      exact ⟨t, ht, ht2⟩
    classical
    let g : Fin r → Fin m := fun x =>
      if hx : x ∈ S ∧ x ∈ X then Classical.choose (hg x hx.1 hx.2) else i
    let T : Finset (Fin m) := insert i (S.image g)
    have hTc : T.card ≤ e + 2 := by
      calc T.card ≤ (S.image g).card + 1 := Finset.card_insert_le _ _
        _ ≤ S.card + 1 := by gcongr; exact Finset.card_image_le
        _ = e + 2 := by rw [hSc]
    let φ := T.orderIsoOfFin rfl
    let f : Fin T.card → Fin m := fun q => (φ q).val
    have hf : StrictMono f := fun a b hab => by
      show (φ a).val < (φ b).val
      exact φ.strictMono hab
    have hpre : ∀ x (hx : x ∈ T), f (φ.symm ⟨x, hx⟩) = x := by
      intro x hx
      show (φ (φ.symm ⟨x, hx⟩)).val = x
      rw [OrderIso.apply_symm_apply]
    have hY := h T.card hTc f hf
    have hk := (key (W ∘ f) X e).1 hY
    let p := φ.symm ⟨i, Finset.mem_insert_self _ _⟩
    have hp : f p = i := hpre _ _
    have hsub : S ⊆ (W ∘ f) p \ X.filter (fun k => ∀ t, p ≤ t → k ∈ (W ∘ f) t) := by
      intro x hx
      have hxW : x ∈ W i := (Finset.mem_sdiff.1 (hS hx)).1
      simp only [Finset.mem_sdiff, Finset.mem_filter, Function.comp, hp, not_and, not_forall]
      refine ⟨hxW, fun hxX => ?_⟩
      have hc := Classical.choose_spec (hg x hx hxX)
      have hgx : g x = Classical.choose (hg x hx hxX) := by
        simp only [g, dite_cond_eq_true (eq_true (And.intro hx hxX))]
      have hT : g x ∈ T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hx)
      refine ⟨φ.symm ⟨g x, hT⟩, ?_, ?_⟩
      · have : f p ≤ f (φ.symm ⟨g x, hT⟩) := by
          rw [hp, hpre]; rw [hgx]; exact hc.1
        exact hf.le_iff_le.1 this
      · rw [hpre, hgx]; exact hc.2
    have := Finset.card_le_card hsub
    have := hk p
    omega


theorem sharp (e : Nat) : ∃ W : Fin (e+2) → Finset (Fin ((e+1)*(e+2))),
    (∀ i j, i < j → e < (W j \ W i).card) ∧
    ¬(∃ Y : Fin (e+2) → Finset (Fin ((e+1)*(e+2))), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ Finset.univ ∧ Y i ⊆ W i ∧ (W i \ Y i).card ≤ e) ∧
    ∀ k : Nat, k < e+2 → ∀ f : Fin k → Fin (e+2), StrictMono f →
      ∃ Y : Fin k → Finset (Fin ((e+1)*(e+2))), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
        ∀ i, Y i ⊆ Finset.univ ∧ Y i ⊆ (W ∘ f) i ∧ ((W ∘ f) i \ Y i).card ≤ e := by
  let Q : Fin (e+2) → Fin (e+1) × Fin (e+2) → Prop := fun j bc =>
    (bc.2.val = 0 ∧ bc.1.val + 1 ≠ j.val) ∨ (0 < bc.2.val ∧ bc.2.val ≤ j.val)
  let W : Fin (e+2) → Finset (Fin ((e+1)*(e+2))) := fun j =>
    Finset.univ.filter (fun x => Q j (finProdFinEquiv.symm x))
  have hmem : ∀ j b c, finProdFinEquiv (b, c) ∈ W j ↔
      ((c.val = 0 ∧ b.val + 1 ≠ j.val) ∨ (0 < c.val ∧ c.val ≤ j.val)) := by
    intro j b c
    simp only [W, Q, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  have hinj : ∀ c : Fin (e+2), Set.InjOn (fun b : Fin (e+1) => finProdFinEquiv (b, c))
      (Finset.univ : Finset (Fin (e+1))) := by
    intro c a _ b _ hab
    have := finProdFinEquiv.injective hab
    simpa using this
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i j hij
    have := Finset.card_le_card_of_injOn (fun b : Fin (e+1) => finProdFinEquiv (b, j))
      (s := Finset.univ) (t := W j \ W i) (fun b _ => by
        simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, hmem]
        have : i.val < j.val := hij
        omega) (hinj j)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  · rw [key]
    intro h
    have h0 := h 0
    have := Finset.card_le_card_of_injOn (fun b : Fin (e+1) => finProdFinEquiv (b, 0))
      (s := Finset.univ)
      (t := W 0 \ Finset.univ.filter (fun k => ∀ t : Fin (e+2), 0 ≤ t → k ∈ W t))
      (fun b _ => by
        simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, hmem, Finset.mem_filter,
          Finset.mem_univ, true_and, not_forall]
        refine ⟨by simp, ⟨b.val + 1, by omega⟩, Fin.zero_le _, ?_⟩
        simp) (hinj 0)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  · intro k hk f hf
    rw [key]
    intro p
    have hsub : W (f p) \ Finset.univ.filter (fun x => ∀ t : Fin k, p ≤ t → x ∈ (W ∘ f) t) ⊆
        (Finset.univ.erase p).image (fun q : Fin k =>
          finProdFinEquiv ((⟨(f q).val - 1, by omega⟩ : Fin (e+1)), (0 : Fin (e+2)))) := by
      intro x hx
      obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective x
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
        Function.comp, hmem] at hx
      obtain ⟨h1, q, hq, h2⟩ := hx
      have hle : (f p).val ≤ (f q).val := hf.monotone hq
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
      have hc : c.val = 0 := by omega
      have hb : b.val + 1 = (f q).val := by omega
      refine ⟨q, ?_, ?_⟩
      · rintro rfl
        omega
      · congr 1
        ext <;> simp <;> omega
    have := Finset.card_le_card hsub
    have h3 := Finset.card_image_le (s := Finset.univ.erase p) (f := fun q : Fin k =>
          finProdFinEquiv ((⟨(f q).val - 1, by omega⟩ : Fin (e+1)), (0 : Fin (e+2))))
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h3
    show (W (f p) \ Finset.univ.filter (fun x => ∀ t : Fin k, p ≤ t → x ∈ (W ∘ f) t)).card ≤ e
    omega

end PEqualNP.Outside.L_lib_1408

theorem PEqualNP.Outside.L_lib_1408 :
(
let trace := fun {r m : Nat} (W : Fin m → Finset (Fin r)) (X : Finset (Fin r)) (e : Nat) =>
  ∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
    ∀ i, Y i ⊆ X ∧ Y i ⊆ W i ∧ (W i \ Y i).card ≤ e
(∀ (r n m : Nat) (W : Fin n → Finset (Fin r)) (L : Fin m → Fin n)
    (X : Finset (Fin r)) (P : Fin n → Finset (Fin r) → Prop),
  (∀ i A B, A ⊆ B → B ⊆ W i → P i A → P i B) →
  let top := fun j : Fin m => X.filter (fun k => ∀ t : Fin m, j ≤ t → k ∈ W (L t))
  let fits := fun (Y : Fin m → Finset (Fin r)) =>
    (∀ i j, i ≤ j → Y i ⊆ Y j) ∧ ∀ i, Y i ⊆ X ∧ Y i ⊆ W (L i) ∧ P (L i) (Y i)
  ((∃ Y, fits Y) ↔ ∀ i, P (L i) (top i)) ∧
  ((∃ Y, fits Y) → fits top ∧ ∀ Y, fits Y → ∀ i, Y i ⊆ top i) ∧
  ∀ e : Nat,
    ((∃ Y : Fin m → Finset (Fin r), (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
      ∀ i, Y i ⊆ X ∧ Y i ⊆ W (L i) ∧ (W (L i) \ Y i).card ≤ e) ↔
      Finset.univ.sup (fun i => (W (L i) \ top i).card) ≤ e)) ∧
(∀ (r m e : Nat) (W : Fin m → Finset (Fin r)) (X : Finset (Fin r)),
  trace W X e ↔ ∀ k : Nat, k ≤ e+2 → ∀ f : Fin k → Fin m, StrictMono f → trace (W ∘ f) X e) ∧
∀ e : Nat, ∃ W : Fin (e+2) → Finset (Fin ((e+1)*(e+2))),
  (∀ i j, i < j → e < (W j \ W i).card) ∧ ¬trace W Finset.univ e ∧
    ∀ k : Nat, k < e+2 → ∀ f : Fin k → Fin (e+2), StrictMono f → trace (W ∘ f) Finset.univ e
) := by
  intro trace
  refine ⟨?_, ?_, ?_⟩
  · intro r n m W L X P hP
    intro top fits
    have G := PEqualNP.Outside.L_lib_1408.gen (fun i => W (L i)) X (fun i => P (L i))
      (fun i A B h1 h2 h3 => hP (L i) A B h1 h2 h3)
    refine ⟨G.1, G.2, fun e => ?_⟩
    rw [PEqualNP.Outside.L_lib_1408.key (fun i => W (L i)) X e, Finset.sup_le_iff]
    simp only [Finset.mem_univ, true_implies]
    rfl
  · intro r m e W X
    exact PEqualNP.Outside.L_lib_1408.sub W X
  · intro e
    exact PEqualNP.Outside.L_lib_1408.sharp e
